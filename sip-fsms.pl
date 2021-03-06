#!/usr/bin/perl
# (c) Pali 2020-2021, Perl license

use strict;
use warnings;

use Encode qw(decode encode);
use Digest::MD5 qw(md5_hex);
use MIME::Base64 qw(encode_base64);
use Storable qw(retrieve store);
use Time::Local qw(timegm timelocal);

use Net::SIP 0.813 qw(create_rtp_sockets invoke_callback ip_canonical laddr4dst sip_hdrval2parts sip_uri2parts);
use Number::Phone::Country 'noexport';
use Number::Phone::Lib;

# Number::Phone::Country does not export functions anymore
sub country_code { goto &Number::Phone::Country::country_code }
sub phone2country { goto &Number::Phone::Country::phone2country }

use constant PI => 4 * atan2(1, 1);

### ITU-T G.711 A-law and u-law compression ###
# ITU-T G.711:
#   https://www.itu.int/rec/T-REC-G.711
#   https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-G.711-198811-I!!PDF-E&type=items

my @alaw_expandtab;
my @alaw_compresstab;
my @ulaw_expandtab;
my @ulaw_compresstab;

for (0..127) {
	my $alaw = ($_ < 16) ? (($_ << 4) + 8) : (((($_ & 0x0F) << 4) + 0x108) << ((($_ >> 4) & 0x07) - 1));
	my $ulaw = (((($_ & 0x0F) << 3) + 0x84) << (($_ & 0x70) >> 4)) - 0x84;
	$alaw_expandtab[$_ ^ 0x55] = -$alaw;
	$alaw_expandtab[($_+128) ^ 0x55] = $alaw;
	$ulaw_expandtab[127-$_] = -$ulaw;
	$ulaw_expandtab[255-$_] = $ulaw;
}

do {
	my $aval = 0;
	my $uval = 0;
	for (0..32767) {
		push @alaw_compresstab, ($aval+128) ^ 0x55;
		unshift @alaw_compresstab, $aval ^ 0x55;
		push @ulaw_compresstab, 255-$uval;
		unshift @ulaw_compresstab, 127-$uval;
		$aval++ if $aval < 127 and $alaw_expandtab[($aval+129) ^ 0x55]-$_ < $_-$alaw_expandtab[($aval+128) ^ 0x55];
		$uval++ if $uval < 127 and $ulaw_expandtab[254-$uval]-$_ < $_-$ulaw_expandtab[255-$uval];
	}
};

### ITU-T V.23 Mode 2 forward channel modem ###
# ITU-T V.23:
#   https://www.itu.int/rec/T-REC-V.23
#   https://www.itu.int/rec/dologin_pub.asp?lang=e&id=T-REC-V.23-198811-I!!PDF-E&type=items

my $v23_freq_mark = 1300;
my $v23_freq_space = 2100;
my $v23_baud_rate = 1200;
my $v23_sample_rate = 8000;

my $v23_phase_base = 2**16;
my $v23_omega_mark = int($v23_phase_base * $v23_freq_mark / $v23_sample_rate);
my $v23_omega_space = int($v23_phase_base * $v23_freq_space / $v23_sample_rate);

my $v23_baud_base = 2**16;
my $v23_baud_incr = int($v23_baud_rate * $v23_baud_base / $v23_sample_rate);

my $v23_cos_base = 5000; # log(5000/32767) * 20 / log(10) ~~ -16.33 dB
my @v23_cos_table = map { int(cos(2 * PI * $_ / $v23_phase_base) * $v23_cos_base) } (0..$v23_phase_base-1);

my $v23_signal_trh = exp(log(10) * -35 / 20); # -35 dB
my $v23_signal_bits = 10;

my $v23_carrier_bits = 20;

my $v23_baud_pll_adj = int($v23_baud_incr / 4);
my $v23_baud_pll_trh = int($v23_baud_base / 4);
my $v23_baud_pll_init = int($v23_baud_base / 2);

my $v23_filter_steps = int($v23_sample_rate / $v23_baud_rate);
my $v23_filter_base = 2; # 2**(fls($v23_filter_steps)-1) = 2**1; sub fls { length(sprintf("%b", $_[0]))-1 }
my $v23_filter_trh = 2**13;

my @v23_filter_mark_i = map { int(cos(2 * PI * $v23_freq_mark * $_ / $v23_sample_rate) * $v23_cos_base) } (0..$v23_filter_steps-1);
my @v23_filter_mark_q = map { int(sin(2 * PI * $v23_freq_mark * $_ / $v23_sample_rate) * $v23_cos_base) } (0..$v23_filter_steps-1);
my @v23_filter_space_i = map { int(cos(2 * PI * $v23_freq_space * $_ / $v23_sample_rate) * $v23_cos_base) } (0..$v23_filter_steps-1);
my @v23_filter_space_q = map { int(sin(2 * PI * $v23_freq_space * $_ / $v23_sample_rate) * $v23_cos_base) } (0..$v23_filter_steps-1);

sub v23_dot_prod {
	my ($v1, $v2) = @_;
	my $prod = 0;
	$prod += $v1->[$_] * $v2->[$_] for 0..$#$v1;
	return $prod;
}

sub v23_encode {
	my ($phase, $baud_pll, $bit) = @_;
	my $omega = $bit ? $v23_omega_mark : $v23_omega_space;
	my @samples;
	while ($baud_pll < $v23_baud_base) {
		$phase = ($phase + $omega) % $v23_phase_base;
		push @samples, $v23_cos_table[$phase];
		$baud_pll += $v23_baud_incr;
	}
	$baud_pll -= $v23_baud_base;
	$_[0] = $phase;
	$_[1] = $baud_pll;
	return @samples;
}

sub v23_decode {
	my ($buffer, $baud_pll, $prevbit, $lastbit, $sample, $synced, $wantbit) = @_;
	push @{$buffer}, int($sample / $v23_filter_base);
	unshift @{$buffer}, 0 until @{$buffer} > $v23_filter_steps;
	shift @{$buffer};
	my $corr_mark_i = int(v23_dot_prod($buffer, \@v23_filter_mark_i) / $v23_cos_base);
	my $corr_mark_q = int(v23_dot_prod($buffer, \@v23_filter_mark_q) / $v23_cos_base);
	my $corr_space_i = int(v23_dot_prod($buffer, \@v23_filter_space_i) / $v23_cos_base);
	my $corr_space_q = int(v23_dot_prod($buffer, \@v23_filter_space_q) / $v23_cos_base);
	my $sum = $corr_mark_i**2 + $corr_mark_q**2 - $corr_space_i**2 - $corr_space_q**2;
	my $newbit = ($sum > $v23_filter_trh) ? 1 : ($sum < -$v23_filter_trh) ? 0 : 2;
	if ($newbit != 2 and $lastbit != $newbit) {
		$lastbit = $newbit;
		$_[3] = $lastbit;
		if (not $synced) {
			$baud_pll = $v23_baud_pll_init;
		} elsif ($baud_pll < $v23_baud_pll_trh) {
			$baud_pll += $v23_baud_pll_adj;
		} elsif ($baud_pll > $v23_baud_base - $v23_baud_pll_trh) {
			$baud_pll -= $v23_baud_pll_adj;
		}
	}
	$baud_pll += $v23_baud_incr;
	$_[1] = $baud_pll;
	if ($baud_pll >= $v23_baud_base and defined $wantbit and $wantbit != $newbit) {
		if ($prevbit == $wantbit) {
			$baud_pll += $v23_baud_incr;
		} else {
			$baud_pll -= $v23_baud_incr;
			$_[2] = $wantbit;
		}
	}
	return if $baud_pll < $v23_baud_base;
	$baud_pll -= $v23_baud_base;
	$_[1] = $baud_pll;
	$_[2] = $newbit;
	return $newbit;
}

sub v23_signal {
	my ($buffer, $sample) = @_;
	push @{$buffer}, ($sample/32767)**2;
	shift @{$buffer} if @{$buffer} > $v23_signal_bits*$v23_filter_steps;
	my $sum = 0;
	$sum += $_ foreach @{$buffer};
	return sqrt($sum / @{$buffer}) > $v23_signal_trh;
}

### Short Message transfer over PSTN/ISDN Protocol 1 ###
# SM-DLL & SM-TL:
#   ETSI ES 201 912 V1.2.1 (2004-08)
#     https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=19813
#     https://www.etsi.org/deliver/etsi_es/201900_201999/201912/01.02.01_60/es_201912v010201p.pdf
# SM-DLL transmission:
#   ETSI EN 300 659-2 V1.3.1 (2001-01)
#     https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=7973
#     https://www.etsi.org/deliver/etsi_en/300600_300699/30065902/01.03.01_60/en_30065902v010301p.pdf
# SM-PL transmission:
#   ETSI EN 300 659-1 V1.3.1 (2001-01)
#     https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=7972
#     https://www.etsi.org/deliver/etsi_en/300600_300699/30065901/01.03.01_60/en_30065901v010301p.pdf
# SM-DLL receiving:
#   ETSI ES 200 778-2 V1.2.2 (2002-11)
#     https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=16160
#     https://www.etsi.org/deliver/etsi_es/200700_200799/20077802/01.02.02_60/es_20077802v010202p.pdf
# SM-PL receiving:
#   ETSI ES 200 778-1 V1.2.2 (2002-11)
#     https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=16158
#     https://www.etsi.org/deliver/etsi_es/200700_200799/20077801/01.02.02_60/es_20077801v010202p.pdf

my $smpl_mark_signal_bits = 80;
my $smpl_mark_signal_bits_min = $smpl_mark_signal_bits-25;
my $smpl_cheksum_mark_bits = 10;

sub smpl_encode {
	my ($phase, $baud_pll, $byte) = @_;
	my @samples;
	push @samples, v23_encode($phase, $baud_pll, 0);
	push @samples, v23_encode($phase, $baud_pll, $_) foreach split //, unpack('b*', chr($byte));
	push @samples, v23_encode($phase, $baud_pll, 1);
	$_[0] = $phase;
	$_[1] = $baud_pll;
	return @samples;
}

my %smdll_types = (
	DATA => 0x11,
	ERROR => 0x12,
	EST => 0x13,
	REL => 0x14,
	ACK => 0x15,
	NACK => 0x16,
);
my %smdll_codes = reverse %smdll_types;

sub smdll_encode {
	my ($noext, $type, $payload) = @_;
	my @payload = defined $payload ? unpack('C*', $payload) : ();
	die "Type for SM-DLL message must be in range 0x00-0x7F\n" unless $type >= 0x00 and $type <= 0x7F;
	die "Payload for SM-DLL message cannot be larger than 176 bytes\n" if @payload > 176;
	$type |= 0b10000000 if $noext;
	my $checksum = 0;
	$checksum += $_ foreach $type, scalar @payload, @payload;
	$checksum = (-$checksum) & 0xFF;
	my @samples;
	my $phase = 0;
	my $baud_pll = 0;
	push @samples, v23_encode($phase, $baud_pll, 1) for 1..$smpl_mark_signal_bits;
	push @samples, smpl_encode($phase, $baud_pll, $type);
	push @samples, smpl_encode($phase, $baud_pll, scalar @payload);
	push @samples, smpl_encode($phase, $baud_pll, $_) foreach @payload;
	push @samples, smpl_encode($phase, $baud_pll, $checksum);
	push @samples, v23_encode($phase, $baud_pll, 1) for 1..$smpl_cheksum_mark_bits;
	return @samples;
}

my %smdll_decode_error_types = (
	NO_ERROR => 0,
	LOST_SIGNAL => 1,
	LOST_CARRIER => 2,
	BROKEN_START_BIT => 3,
	BROKEN_STOP_BIT => 4,
	WRONG_CHECKSUM => 5,
	WRONG_LENGTH => 6,
);
my %smdll_decode_error_codes = reverse %smdll_decode_error_types;

sub smdll_decode {
	my ($state, $sample) = @_;
	my $had_carrier = (defined $state->{carrier_bits} and $state->{carrier_bits} >= $v23_carrier_bits);
	$state->{signal_buffer} = [] unless exists $state->{signal_buffer};
	my $has_signal = v23_signal($state->{signal_buffer}, $sample);
	if (not $has_signal) {
		$state->{had_signal} = 0;
		$state->{mark_bits} = 0;
		$state->{had_mark_signal} = 0;
		return $state->{had_mark_signal} ? $smdll_decode_error_types{LOST_SIGNAL} : ();
	} elsif (not $state->{had_signal}) {
		$state->{had_signal} = 1;
		$state->{filter_buffer} = [];
		$state->{baud_pll} = 0;
		$state->{prevbit} = 2;
		$state->{lastbit} = 2;
		$state->{carrier_bits} = 0;
		$state->{mark_bits} = 0;
		$state->{had_mark_signal} = 0;
		$state->{skip_mark_bits} = 0;
		$state->{smdll_bits} = [];
		$state->{smdll_buffer} = [];
	}
	my $wantbit = (@{$state->{smdll_bits}} == 0 ? 0 : @{$state->{smdll_bits}} == 9 ? 1 : undef);
	my $newbit = v23_decode($state->{filter_buffer}, $state->{baud_pll}, $state->{prevbit}, $state->{lastbit}, $sample, $state->{had_mark_signal}, $wantbit);
	if (defined $newbit) {
		if ($newbit == 0 or $newbit == 1) {
			$state->{carrier_bits}++;
		} else {
			$state->{carrier_bits} = 0;
		}
		if ($state->{skip_mark_bits} > 0) {
			if ($newbit == 1) {
				$newbit = undef;
				$state->{skip_mark_bits}--;
			} else {
				$state->{skip_mark_bits} = 0;
			}
		}
	}
	return unless defined $newbit;
	my $has_carrier = $state->{carrier_bits} >= $v23_carrier_bits;
	if (not $has_carrier) {
		my $has_mark_signal = $state->{had_mark_signal};
		$state->{mark_bits} = 0;
		$state->{had_mark_signal} = 0;
		$state->{skip_mark_bits} = 0;
		return $has_mark_signal ? $smdll_decode_error_types{LOST_CARRIER} : ();
	} elsif (not $had_carrier) {
		$state->{mark_bits} = 0;
		$state->{had_mark_signal} = 0;
		$state->{smdll_bits} = [];
		$state->{smdll_buffer} = [];
	}
	if (not $state->{had_mark_signal}) {
		if ($newbit == 1) {
			$state->{mark_bits}++;
		} elsif ($state->{mark_bits} >= $smpl_mark_signal_bits_min) {
			$state->{had_mark_signal} = 1;
		} else {
			$state->{mark_bits} = 0;
		}
	}
	return unless $state->{had_mark_signal};
	if (@{$state->{smdll_bits}} == 9) {
		if ($newbit != 1) {
			$state->{mark_bits} = 0;
			$state->{had_mark_signal} = 0;
			$state->{smdll_buffer} = [];
			return $smdll_decode_error_types{BROKEN_STOP_BIT};
		}
		push @{$state->{smdll_buffer}}, ord(pack('b*', join '', @{$state->{smdll_bits}}[1..8]));
		$state->{smdll_bits} = [];
	} else {
		if (@{$state->{smdll_bits}} == 0 and $newbit != 0) {
			$state->{mark_bits} = 0;
			$state->{had_mark_signal} = 0;
			$state->{smdll_buffer} = [];
			return $smdll_decode_error_types{BROKEN_START_BIT};
		}
		push @{$state->{smdll_bits}}, $newbit;
	}
	return unless @{$state->{smdll_buffer}} >= 2;
	my $length = $state->{smdll_buffer}->[1];
	return unless @{$state->{smdll_buffer}} == $length + 3;
	my $checksum = pop @{$state->{smdll_buffer}};
	my $exp_checksum = 0;
	$exp_checksum += $_ foreach @{$state->{smdll_buffer}};
	$exp_checksum = (-$exp_checksum) & 0xFF;
	my $type = shift @{$state->{smdll_buffer}};
	my $noext = ($type & 0b10000000) ? 1 : 0;
	$type &= 0b01111111;
	shift @{$state->{smdll_buffer}};
	my $payload = ($length > 0) ? pack('C*', @{$state->{smdll_buffer}}) : undef;
	my $status = $smdll_decode_error_types{NO_ERROR};
	$status = $smdll_decode_error_types{WRONG_LENGTH} if $length > 176;
	$status = $smdll_decode_error_types{WRONG_CHECKSUM} if $checksum != $exp_checksum;
	$state->{mark_bits} = 0;
	$state->{had_mark_signal} = 0;
	$state->{skip_mark_bits} = 10;
	$state->{smdll_buffer} = [];
	return $status, $noext, $type, $payload, $checksum;
}

my %smdll_error_types = (
	WRONG_CHECKSUM => 0x01,
	WRONG_LENGTH => 0x02,
	UNKNOWN_TYPE => 0x03,
	UNSUPP_EXT => 0x04,
	UNSPEC_CAUSE => 0xFF,
);
my %smdll_error_codes = reverse %smdll_error_types;

sub smdll_encode_error {
	my ($code) = @_;
	return smdll_encode(1, $smdll_types{ERROR}, chr($code));
}

sub smdll_encode_est {
	return smdll_encode(1, $smdll_types{EST});
}

sub smdll_encode_rel {
	return smdll_encode(1, $smdll_types{REL});
}

sub smdll_encode_ack {
	my ($tpdu) = @_;
	die "TPDU for ACK SM-DLL message cannot be larger than 176 bytes\n" if defined $tpdu and length $tpdu > 176;
	return smdll_encode(1, $smdll_types{ACK}, $tpdu);
}

sub smdll_encode_nack {
	my ($tpdu) = @_;
	die "TPDU for NACK SM-DLL message cannot be larger than 176 bytes\n" if defined $tpdu and length $tpdu > 176;
	return smdll_encode(1, $smdll_types{NACK}, $tpdu);
}

sub smtl_decode_data {
	my ($smtl_buffer, $noext, $type, $payload) = @_;
	return $payload unless $type == $smdll_types{DATA};
	if (not $noext) {
		${$smtl_buffer} = '' unless defined ${$smtl_buffer};
		${$smtl_buffer} .= $payload;
		return;
	}
	if ($noext and defined ${$smtl_buffer}) {
		$payload = ${$smtl_buffer} . $payload;
		${$smtl_buffer} = undef;
	}
	return $payload;
}

sub smtl_encode_data {
	my ($tpdu) = @_;
	my @payloads = defined $tpdu ? unpack('(A176)*', $tpdu) : ();
	my $last_payload = pop @payloads;
	my @samples;
	push @samples, [ smdll_encode(0, $smdll_types{DATA}, $_) ] foreach @payloads;
	push @samples, [ smdll_encode(1, $smdll_types{DATA}, $last_payload) ];
	return @samples;
}

### GSM Short Message Transfer Layer ###
# SM-TL/TPDU:
#   3GPP TS 23.040
#     https://www.3gpp.org/dynareport/23040.htm
#     ETSI TS 123 040 V16.0.0 (2020-07)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=60072
#       https://www.etsi.org/deliver/etsi_ts/123000_123099/123040/16.00.00_60/ts_123040v160000p.pdf
#     ETSI TS 123 040 V3.5.0 (2000-07)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=11369
#       https://www.etsi.org/deliver/etsi_ts/123000_123099/123040/03.05.00_60/ts_123040v030500p.pdf
#   GSM 03.40
#     https://www.3gpp.org/dynareport/0340.htm
#     ETSI GTS 03.40 V3.7.0 (1995-01)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=1546
#       https://www.etsi.org/deliver/etsi_gts/03/0340/03.07.00_60/gsmts_0340sv030700p.pdf
# TP-DCS & 7bit enc:
#   3GPP TS 23.038
#     https://www.3gpp.org/dynareport/23038.htm
#     ETSI TS 123 038 V16.0.0 (2020-07)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=60070
#       https://www.etsi.org/deliver/etsi_ts/123000_123099/123038/16.00.00_60/ts_123038v160000p.pdf
# TP-UD compression:
#   3GPP TS 23.042
#     https://www.3gpp.org/dynareport/23042.htm
#     ETSI TS 123 042 V16.0.0 (2020-07)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=60075
#       https://www.etsi.org/deliver/etsi_ts/123000_123099/123042/16.00.00_60/ts_123042v160000p.pdf

my @tpdu_bcd_digits_dec_tab = ('0'..'9', ('0') x 6);
my @tpdu_bcd_dec_tab = ('0'..'9', '*', '#', 'a'..'c', '');
my %tpdu_bcd_enc_tab = map{ (lc $tpdu_bcd_dec_tab[$_] => $_, uc $tpdu_bcd_dec_tab[$_] => $_)  } (0..$#tpdu_bcd_dec_tab);

sub tpdu_decode_semioctet {
	my $h1 = ord($_[0]) & 0b00001111;
	my $h2 = (ord($_[0]) & 0b11110000) >> 4;
	return $tpdu_bcd_dec_tab[$h1] . $tpdu_bcd_dec_tab[$h2];
}

sub tpdu_decode_semioctet_digits {
	my $h1 = ord($_[0]) & 0b00001111;
	my $h2 = (ord($_[0]) & 0b11110000) >> 4;
	return $tpdu_bcd_digits_dec_tab[$h1] . $tpdu_bcd_digits_dec_tab[$h2];
}

sub tpdu_encode_semioctet {
	my $h1 = substr $_[0], 0, 1;
	my $h2 = substr $_[0], 1, 1;
	my $t1 = exists $tpdu_bcd_enc_tab{$h1} ? $tpdu_bcd_enc_tab{$h1} : $tpdu_bcd_enc_tab{''};
	my $t2 = exists $tpdu_bcd_enc_tab{$h2} ? $tpdu_bcd_enc_tab{$h2} : $tpdu_bcd_enc_tab{''};
	return chr($t1 | ($t2 << 4));
}

sub tpdu_decode_7bit {
	return encode('UTF-8', decode('GSM0338', substr(pack('(b*)*', unpack '(A7)*', unpack 'b*', $_[0]), 0, $_[1])));
}

sub tpdu_encode_7bit {
	my $bytes = encode('GSM0338', decode('UTF-8', $_[0]));
	my $len = length $bytes;
	my $septets = pack 'b*', join '', map { substr $_, 0, 7 } unpack '(A8)*', unpack 'b*', $bytes;
	return ($septets, $len);
}

sub tpdu_decode_address {
	my ($address) = @_;
	return unless length $address >= 2;
	my $number_len = ord(substr $address, 0, 1);
	my $address_type = ord(substr $address, 1, 1);
	my $number_type = ($address_type & 0b01110000) >> 4;
	my $number_plan = ($address_type & 0b00001111);
	my $address_len = 2 + int(($number_len+1)/2);
	return unless $address_len <= 12;
	return unless length $address >= $address_len;
	my $address_value = substr $address, 2, $address_len-2;
	my $number_value;
	if ($number_type == 0b101) {
		$number_value = tpdu_decode_7bit($address_value, $address_len-2);
	} elsif ($number_type == 0b000 and $number_plan == 0b1001) {
		# Special undocumented GSM 7bit encoding for F-SMS TPDU address used in Czech Republic:
		# Bytes are encoded as half-octets, first encoded byte represents number of GSM 7bit septets
		# and the rest encoded bytes contain GSM 7bit septets packed as bytes
		$address_value = join '', map { chr(((ord($_) & 0b00001111) << 4) | ((ord($_) & 0b11110000) >> 4)) } split //, $address_value;
		my $septets_len = ord(substr $address_value, 0, 1, '');
		$septets_len = $address_len-2 if $septets_len > $address_len-2;
		$number_value = tpdu_decode_7bit($address_value, $septets_len);
		$number_type = 0b101;
	} else {
		$number_value = substr(join('', map { tpdu_decode_semioctet($_) } split //, $address_value), 0, $number_len);
	}
	$number_value = "+$number_value" if $number_type == 0b001 and $number_value =~ /^[1-9][0-9]+$/;
	return ([$number_value, $number_type, $number_plan], $address_len);
}

sub tpdu_encode_address {
	my ($number, $type, $plan) = @_;
	$type = ($number =~ /^(?:\+|00)[1-9][0-9]+$/) ? 0b001 : ($number =~ /^[0-9]+$/) ? 0b000 : 0b101 unless defined $type;
	$plan = ($number =~ /^\+?[0-9]+$/) ? 0b0001 : 0b0000 unless defined $plan;
	$number = $1 if $number =~ /^(?:\+|00)([1-9][0-9]+)$/ and $type == 0b001;
	die "TPDU number type $type is not in range 0b000 ... 0b111\n" if $type < 0 or $type > 0b111;
	die "TPDU number plan $plan is not in range 0b0000 ... 0b1111\n" if $plan < 0 or $plan > 0b1111;
	my ($sep, $sep_len) = ($type == 0b101) ? tpdu_encode_7bit($number) : ();
	my $address = '';
	$address .= chr($type == 0b101 ? ($sep_len*7+3)/4 : length $number);
	$address .= chr(0b10000000 | ($type << 4) | $plan);
	if ($type == 0b101) {
		$address .= $sep;
	} else {
		die "TPDU number type $type cannot contain non-numeric characters\n" unless $number =~ /^[0-9*#a-cA-C]*$/;
		$address .= tpdu_encode_semioctet($_) foreach unpack '(A2)*', $number;
	}
	die "TPDU number is too long\n" unless length $address <= 12;
	return $address;
}

sub tpdu_is_fragmented {
	my ($tpdu) = @_;
	return unless length $tpdu > 0;
	my $first = ord(substr $tpdu, 0, 1);
	my $has_udh = ($first & 0b01000000) ? 1 : 0;
	return unless $has_udh;
	my $mti = ($first & 0b00000011);
	my $vpf = ($mti == 1) ? (($first & 0b00011000) >> 3) : 0;
	my $offset = 1;
	$offset += 1 unless $mti == 0 or $mti == 3;
	my ($num, $addr_len) = tpdu_decode_address(substr $tpdu, $offset);
	return unless defined $num and $addr_len > 0;
	$offset += $addr_len;
	$offset += 15 if $mti == 2;
	$offset += 2;
	$offset += 7 if $mti == 0 or $mti == 3;
	$offset += 1 if $vpf == 2;
	$offset += 7 if $vpf == 3 or $vpf == 1;
	return unless length $tpdu > $offset;
	my $udl = ord(substr $tpdu, $offset, 1);
	$offset += 1;
	return unless length $tpdu > $offset;
	my $udhl = ord(substr $tpdu, $offset, 1);
	$offset += 1;
	return unless length $tpdu >= $offset + $udhl;
	my $udh = substr $tpdu, $offset, $udhl;
	$offset = 0;
	my ($ref_num, $max_num, $seq_num);
	while (length $udh >= $offset + 2) {
		my $udh_ei = ord(substr $udh, $offset++, 1);
		my $udh_el = ord(substr $udh, $offset++, 1);
		last unless length $udh >= $offset + $udh_el;
		my $udh_ed = substr $udh, $offset, $udh_el;
		$offset += $udh_el;
		next unless $udh_ei == 0x00 or $udh_ei == 0x16;
		next if $udh_ei == 0x00 and $udh_el != 3;
		next if $udh_ei == 0x16 and $udh_el != 4;
		$ref_num = ord(substr $udh_ed, 0, 1, '');
		$ref_num = ($ref_num << 8) | ord(substr $udh_ed, 0, 1, '') if $udh_ei == 0x16;
		$max_num = ord(substr $udh_ed, 0, 1, '');
		$seq_num = ord(substr $udh_ed, 0, 1, '');
	}
	return unless defined $ref_num;
	return [ $mti, $num->[0], $ref_num, $max_num, $seq_num ];
}

sub tpdu_decode_ts {
	my ($ts) = @_;
	return unless length $ts == 7;
	my @ts = split //, $ts;
	my $sign = (ord($ts[6]) & 0b00001000) ? '-' : '+';
	$ts[6] = chr(ord($ts[6]) & 0b11110111);
	my @nums = map { tpdu_decode_semioctet_digits($_) } @ts;
	$nums[0] = ($nums[0] < 70) ? "20$nums[0]" : "19$nums[0]";
	my $tz = $nums[6] * 15;
	$sign = '' unless $tz;
	return [ @nums[0..5], $sign, sprintf('%02u', int($tz/60)), sprintf('%02u', $tz%60) ];
}

sub tpdu_encode_ts {
	my (@ts) = @_;
	die "TPDU timestamp must contain 9 elements\n" unless @ts == 9;
	substr $ts[0], 0, -2, '';
	my $sign = splice @ts, 6, 1;
	$sign = '' if $sign eq '+';
	die "TPDU timestamp timezone sign is invalid\n" unless $sign eq '-' or $sign eq '';
	die "TPDU timestamp elements must contain 2 digits\n" unless 8 == grep { $_ =~ /^[0-9]{1,2}$/ } @ts;
	my ($hours, $minutes) = splice @ts, 6, 2;
	push @ts, int(($hours*60 + $minutes)/15);
	die "TPDU timestamp timezone is invalid\n" unless $ts[6] <= 79;
	my $ts = '';
	$ts .= tpdu_encode_semioctet($_) foreach unpack '(A2)*', join '', map { sprintf '%02u', $_ } @ts;
	substr $ts, 6, 1, chr(ord(substr $ts, 6, 1) | 0b00001000) if $sign eq '-';
	return $ts;
}

sub tpdu_decode_vp {
	my ($vp, $vpf) = @_;
	return unless defined $vpf;
	if ($vpf == 0) {
		return ([0, 0], 0);
	} elsif ($vpf == 2) {
		return unless length $vp >= 1;
		my $num = ord(substr $vp, 0, 1);
		if ($num <= 143) {
			$num = ($num+1)*5*60;
		} elsif ($num <= 167) {
			$num = 12*60*60 + ($num-143)*30*60;
		} elsif ($num <= 196) {
			$num = ($num-166)*24*60*60;
		} else {
			$num = ($num-192)*7*24*60*60;
		}
		return ([0, 1, $num], 1);
	} elsif ($vpf == 3) {
		return unless length $vp >= 7;
		return ([0, 2, tpdu_decode_ts(substr $vp, 0, 7)], 7);
	} elsif ($vpf == 1) {
		return unless length $vp >= 7;
		my $vpi = ord(substr $vp, 0, 1);
		my $ext = ($vpi & 0b10000000) ? 1 : 0;
		my $single = ($vpi & 0b01000000) ? 1 : 0;
		my $format = ($vpi & 0b00000111);
		if ($format == 0) {
			return ([$single, 0], 7);
		} elsif ($ext) {
			return ([$single, 0], 7);
		} elsif ($format == 1) {
			my ($rel, undef) = tpdu_decode_vp(substr($vp, 1, 1), 2);
			return ([$single, 1, $rel->[2]], 7);
		} elsif ($format == 2) {
			return ([$single, 1, ord(substr $vp, 1, 1)], 7);
		} elsif ($format == 3) {
			my @time = map { tpdu_decode_semioctet_digits($_) } split //, substr $vp, 1, 3;
			return ([$single, 1, $time[0]*60*60 + $time[1]*60 + $time[2]], 7);
		} else {
			return ([$single, 0], 7);
		}
	} else {
		return;
	}
}

sub tpdu_encode_vp {
	my (@vp) = @_;
	return (0, '') unless @vp;
	die "TPDU validity period must contain 3 elements\n" unless @vp == 3;
	my $vpf;
	my $vp;
	if ($vp[1] == 2) {
		die "TPDU single shot cannot be used for absolute validity period\n" if $vp[0];
		$vpf = 3;
		$vp = tpdu_encode_ts(@{$vp[2]});
	} elsif (not $vp[0] and $vp[1] == 1 and $vp[2] <= (143+1)*5*60 and $vp[2] % (5*60) == 0) {
		$vpf = 2;
		$vp = chr(int($vp[2]/(5*60))+1);
	} elsif (not $vp[0] and $vp[1] == 1 and $vp[2] >= 12*60*60 + (144-143)*30*60 and $vp[2] <= 12*60*60 + (167-143)*30*60 and ($vp[2] - 12*60*60) % (30*60) == 0) {
		$vpf = 2;
		$vp = chr(int(($vp[2] - 12*60*60) / (30*60)) + 143);
	} elsif (not $vp[0] and $vp[1] == 1 and $vp[2] >= (168-166)*24*60*60 and $vp[2] <= (196-166)*24*60*60) {
		$vpf = 2;
		$vp = chr(int($vp[2]/(24*60*60)) + 166);
	} elsif (not $vp[0] and $vp[1] == 1 and $vp[2] >= (167-192)*7*24*60*60 and $vp[2] <= (255-192)*7*24*60*60) {
		$vpf = 2;
		$vp = chr(int($vp[2]/(7*24*60*60)) + 192);
	} elsif (not $vp[0] and $vp[1] == 1 and $vp[2] > (255-192)*7*24*60*60) {
		$vpf = 2;
		$vp = chr(255);
	} elsif (not $vp[0] and $vp[1] == 0) {
		$vpf = 0;
		$vp = '';
	} else {
		$vpf = 1;
		my $vpi = 0;
		$vpi |= 0b01000000 if $vp[0];
		if ($vp[1] == 0) {
			$vpi |= 0b00000000;
		} elsif ($vp[2] < 256) {
			$vpi |= 0b00000010;
			$vp = chr($vp[2]);
		} elsif ($vp[2] < 24*60*60) {
			$vpi |= 0b00000011;
			$vp = '';
			$vp .= tpdu_encode_semioctet(sprintf "%02u", int($vp[2]/(60*60)));
			$vp .= tpdu_encode_semioctet(sprintf "%02u", int($vp[2]/60) % 60);
			$vp .= tpdu_encode_semioctet(sprintf "%02u", $vp[2] % 60);
		} else {
			$vpi |= 0b00000001;
			if ($vp[2] <= (196-166)*24*60*60) {
				$vp = chr(int($vp[2]/(24*60*60)) + 166);
			} elsif ($vp[2] <= (255-192)*7*24*60*60) {
				$vp = chr(int($vp[2]/(7*24*60*60)) + 192);
			} else {
				$vp = chr(255);
			}
		}
		$vp = chr($vpi) . $vp;
		$vp .= chr(0) x (7-length($vp));
	}
	return ($vpf, $vp);
}

sub tpdu_decode_st {
	my $st = ord($_[0]);
	$st = 0b01100011 if $st & 0b10000000;
	return [($st >> 5), ($st & 0b00011111)];
}

sub tpdu_encode_st {
	return chr((($_[0] & 0b00000111) << 5) | ($_[1] & 0b00011111));
}

sub tpdu_decode_dcs {
	my $dcs = ord($_[0]);
	my $mc = ((($dcs & 0b10010000) == 0b00010000) || (($dcs & 0b11110000) == 0b11110000)) ? ($dcs & 0b00000011) : undef;
	my $cd = (($dcs & 0b10100000) == 0b00100000) ? 1 : 0;
	my $ad = (($dcs & 0b11000000) == 0b01000000) ? 1 : 0;
	my $it = ((($dcs & 0b11100000) == 0b11000000) || (($dcs & 0b11110000) == 0b11100000)) ? ($dcs & 0b00000011) : undef;
	my $is = ((($dcs & 0b11100000) == 0b11000000) || (($dcs & 0b11110000) == 0b11100000)) ? (($dcs & 0b00001000) ? 1 : 0) : undef;
	my $id = ((($dcs & 0b11100000) == 0b11000000) || (($dcs & 0b11110000) == 0b11100000)) ? ((($dcs & 0b11110000) == 0b11000000) ? 1 : 0) : undef;
	my $is_ucs2 = ((((($dcs & 0b10000000) == 0b00000000) || (($dcs & 0b11110000) == 0b11110000)) && (($dcs & 0b00001100) == 0b00001000)) || (($dcs & 0b11110000) == 0b11100000)) ? 1 : 0;
	my $is_8bit = (((($dcs & 0b10000000) == 0b00000000) || (($dcs & 0b11110000) == 0b11110000)) && (($dcs & 0b00001100) == 0b00000100)) ? 1 : 0;
	return ($mc, $ad, (defined $it ? [$it, undef, $is, $id, undef] : undef), ($is_ucs2 ? 2 : $is_8bit ? 1 : 0), $cd);
}

sub tpdu_encode_dcs {
	my ($mc, $ad, $mwi, $ud_isbin, $data) = @_;
	die "TPDU message class and message waiting indicator cannot be used together\n" if defined $mc and defined $mwi;
	die "TPDU binary data cannot contain wide characters\n" if $ud_isbin and $data =~ /[^\x00-\xff]/;
	my $ud_enc = $ud_isbin ? 1 : eval { encode('GSM0338', decode('UTF-8', $data), 1); 1 } ? 0 : 2;
	my $dcs = 0;
	if (defined $mwi) {
		$dcs |= 0b11000000;
		$dcs |= ($mwi->[0] & 0b11);
		$dcs |= 0b00001000 if $mwi->[1];
		die "TPDU message waiting indicator cannot be used with binary data\n" if $ud_enc == 1;
		die "TPDU message waiting indicator and automatic deletion cannot be used with UCS-2 data\n" if $ad and $ud_enc == 2;
		$dcs |= ($ud_enc == 2 ? 0b00100000 : 0b00010000) unless $ad;
	} else {
		if (defined $mc) {
			$dcs |= 0b00010000;
			$dcs |= $mc;
		}
		$dcs |= 0b01000000 if $ad;
		$dcs |= ($ud_enc << 2);
	}
	return (chr($dcs), $ud_enc);
}

sub tpdu_decompress_ud {
	# TODO
	return 'UNSUPPORTED COMPRESSED DATA: ' . join '', map { sprintf '\\x%02x', ord($_) } split //, $_[0];
}

sub tpdu_compress_ud {
	# TODO
}

sub tpdu_decode_ud {
	my ($ud, $has_udh, $udl, $ud_enc, $ud_cd) = @_;
	my ($mwis, $port, $wcmp, $ehl, $ra, $nlss, $nlls);
	my $fragmented;
	if ($has_udh) {
		return unless length $ud >= 1;
		my $udhl = ord(substr $ud, 0, 1, '');
		return unless length $ud >= $udhl;
		my $udh = substr $ud, 0, $udhl, '';
		while (length $udh >= 2) {
			my $udh_ei = ord(substr $udh, 0, 1, '');
			my $udh_el = ord(substr $udh, 0, 1, '');
			last unless length $udh >= $udh_el;
			my $udh_ed = substr $udh, 0, $udh_el, '';
			if ($udh_ei == 0x00 or $udh_ei == 0x08) { # Concatenated short messages
				$fragmented = 1;
			} elsif ($udh_ei == 0x01 and $udh_el == 2) { # Special SMS Message Indication
				my $first = ord(substr $udh_ed, 0, 1, '');
				my $count = ord(substr $udh_ed, 0, 1, '');
				my $type = ($first & 0b00000011);
				my $type_ext = ($first & 0b00011100) >> 2;
				my $profile = ($first & 0b01100000) >> 5;
				my $discard = ($first & 0b10000000) ? 1 : 0;
				$mwis = [] unless defined $mwis;
				push @{$mwis}, [$type, $type_ext, $count, $discard, $profile];
			} elsif (($udh_ei == 0x04 and $udh_el == 2) or ($udh_ei == 0x05 and $udh_el == 4)) { # Application port addressing scheme
				my $dp = ord(substr $udh_ed, 0, 1, '');
				$dp = ($dp << 8) | ord(substr $udh_ed, 0, 1, '') if $udh_ei == 0x05;
				my $op = ord(substr $udh_ed, 0, 1, '');
				$op = ($op << 8) | ord(substr $udh_ed, 0, 1, '') if $udh_ei == 0x05;
				$port = [ $dp, $op ];
			} elsif ($udh_ei == 0x09) { # Wireless Control Message Protocol
				$wcmp = $udh_ed;
			} elsif ($udh_ei == 0x20 and $udh_el == 1) { # RFC 5322 E-Mail Header
				$ehl = ord($udh_ed);
			} elsif ($udh_ei == 0x22) { # Reply Address Element
				($ra) = tpdu_decode_address($udh_ed);
			} elsif ($udh_ei == 0x23) { # Enhanced Voice Mail Information
				# TODO
			} elsif ($udh_ei == 0x24 and $udh_el == 1) { # National Language Single Shift
				$nlss = ord($udh_ed);
			} elsif ($udh_ei == 0x25 and $udh_el == 1) { # National Language Locking Shift
				$nlls = ord($udh_ed);
			}
		}
		$udl -= $udhl+1;
		if ($ud_enc == 2) {
			substr $ud, 0, ($udhl+1)%2, '';
		} elsif ($ud_enc == 0) {
			my $plen = (7-(($udhl+1)*8)%7)%7;
			$ud = pack 'b*', substr unpack('b*', $ud), $plen if $plen;
			$udl -= $plen;
		}
	}
	if ($ud_cd) {
		$ud = substr $ud, 0, $udl;
		$ud = tpdu_decompress_ud($ud) unless $fragmented;
	} elsif ($ud_enc == 2) {
		my $bom = (length $ud >= 2) ? (substr $ud, 0, 2, '') : '';
		my $enc;
		if ($bom eq "\xFF\xFE") {
			$enc = 'UTF-16LE';
			$udl -= 2;
		} elsif ($bom eq "\xFE\xFF") {
			$enc = 'UTF-16BE';
			$udl -= 2;
		} else {
			$enc = 'UTF-16BE';
			$ud = $bom.$ud;
		}
		$ud = encode('UTF-8', decode($enc, substr $ud, 0, $udl));
	} elsif ($ud_enc == 1) {
		$ud = substr $ud, 0, $udl;
	} else {
		# TODO: decode using $nlss and $nlls
		$ud = tpdu_decode_7bit($ud, $udl);
	}
	return ($ud, $mwis, $port, $wcmp, $ehl, $ra);
}

sub tpdu_encode_ud {
	my ($udh, $ud_enc, $data) = @_;
	$udh = '' unless defined $udh;
	$data = '' unless defined $data;
	my ($ud, $udl);
	if ($ud_enc == 2) {
		$ud = encode('UTF-16BE', decode('UTF-8', $data));
		$udl = length $ud;
	} elsif ($ud_enc == 1) {
		$ud = $data;
		$udl = length $ud;
	} else {
		($ud, $udl) = tpdu_encode_7bit($data);
	}
	if (length $udh) {
		if ($ud_enc == 2 and length($udh) % 2 == 1) {
			$udh .= chr(0);
		} elsif ($ud_enc == 0) {
			my $plen = (7-(length($udh)*8)%7)%7;
			$ud = pack 'b*', ('0' x $plen) . unpack 'b*', $ud if $plen;
		}
		$udl += ($ud_enc == 0) ? (length($udh)*8+6)/7 : length($udh);
	}
	die "TPDU user data are larger than 140 bytes\n" if length($udh) + length($ud) > 140;
	return chr($udl) . $udh . $ud;
}

sub tpdu_decode {
	my ($tpdu) = @_;
	return unless length $tpdu >= 1;
	my $first = ord(substr $tpdu, 0, 1, '');
	my $mti = ($first & 0b00000011);
	my $is_deliver = $mti == 0 || $mti == 3;
	my $is_submit = $mti == 1;
	my $is_status = $mti == 2;
	my $mms = $is_submit ? undef : (($first & 0b00000100) ? 0 : 1);
	my $rd = $is_submit ? (($first & 0b00000100) ? 1 : 0) : undef;
	my $vpf = $is_submit ? (($first & 0b00011000) >> 3) : undef;
	my $lp = $is_submit ? undef : (($first & 0b00001000) >> 3);
	my $sr = ($first & 0b00010000) ? 1 : 0;
	my $has_udh = ($first & 0b01000000) ? 1 : 0;
	my $rp = $is_status ? undef : (($first & 0b10000000) ? 1 : 0);
	return unless length $tpdu >= 1;
	my $mr = $is_deliver ? undef : ord(substr $tpdu, 0, 1, '');
	my ($num, $addr_len) = tpdu_decode_address($tpdu);
	return unless defined $num;
	substr $tpdu, 0, $addr_len, '';
	my ($scts, $dt, $st);
	if ($is_status) {
		return unless length $tpdu >= 7+7+1;
		$scts = tpdu_decode_ts(substr $tpdu, 0, 7, '');
		$dt = tpdu_decode_ts(substr $tpdu, 0, 7, '');
		$st = tpdu_decode_st(substr $tpdu, 0, 1, '');
	}
	return unless length $tpdu >= 1;
	my $pid = ord(substr $tpdu, 0, 1, '');
	return unless length $tpdu >= 1;
	my ($mc, $ad, $mwi, $ud_enc, $ud_cd) = tpdu_decode_dcs(substr $tpdu, 0, 1, '');
	my $ud_isbin = ($ud_enc == 1);
	if ($is_deliver) {
		return unless length $tpdu >= 7;
		$scts = tpdu_decode_ts(substr $tpdu, 0, 7, '');
	}
	my $vp;
	if (defined $vpf) {
		my $vp_len;
		($vp, $vp_len) = tpdu_decode_vp($tpdu, $vpf);
		return unless defined $vp_len;
		substr $tpdu, 0, $vp_len, '';
	}
	return unless length $tpdu >= 1;
	my $udl = ord(substr $tpdu, 0, 1, '');
	my ($ud, $mwis, $port, $wcmp, $ehl, $ra) = tpdu_decode_ud($tpdu, $has_udh, $udl, $ud_enc, $ud_cd);
	if (defined $mwi and defined $mwis) {
		foreach (@{$mwis}) {
			next unless $mwi->[0] == $_->[0];
			undef $mwi;
			last;
		}
		unshift @{$mwis}, $mwi if defined $mwi;
	} elsif (defined $mwi) {
		$mwis = [$mwi];
		undef $mwi;
	}
	return ($mti, $mms, $rd, $lp, $sr, $rp, $mr, $num, $scts, $dt, $st, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud);
}

sub tpdu_decode_report {
	my ($tpdu, $is_nack) = @_;
	return unless length $tpdu >= 1;
	my $first = ord(substr $tpdu, 0, 1, '');
	my $mti = ($first & 0b00000011);
	my $has_udh = ($first & 0b01000000) ? 1 : 0;
	return unless $mti == 0 or $mti == 1;
	my $fcs;
	if ($is_nack) {
		return unless length $tpdu >= 1;
		$fcs = ord(substr $tpdu, 0, 1, '');
	}
	return unless length $tpdu >= 1;
	my $pi = ord(substr $tpdu, 0, 1, '');
	my $has_pid = ($pi & 0b00000001) ? 1 : 0;
	my $has_dcs = ($pi & 0b00000010) ? 1 : 0;
	my $has_udl = ($pi & 0b00000100) ? 1 : 0;
	my $has_pi_ext = ($pi & 0b10000000) ? 1 : 0;
	while ($has_pi_ext) {
		return unless length $tpdu >= 1;
		$pi = ord(substr $tpdu, 0, 1, '');
		$has_pi_ext = ($pi & 0b10000000) ? 1 : 0;
	}
	my ($scts, $pid, $mc, $ad, $mwi, $ud_enc, $ud_cd, $ud_isbin, $udl, $ud, $mwis, $port, $wcmp, $ehl, $ra);
	if ($mti == 1) {
		return unless length $tpdu >= 7;
		$scts = tpdu_decode_ts(substr $tpdu, 0, 7, '');
	}
	if ($has_pid) {
		return unless length $tpdu >= 1;
		$pid = ord(substr $tpdu, 0, 1, '');
	}
	if ($has_dcs) {
		return unless length $tpdu >= 1;
		($mc, $ad, $mwi, $ud_enc, $ud_cd) = tpdu_decode_dcs(substr $tpdu, 0, 1, '');
		$ud_isbin = ($ud_enc == 1);
	}
	if ($has_udl) {
		return unless length $tpdu >= 1;
		$udl = ord(substr $tpdu, 0, 1, '');
	} elsif ($ud_enc) {
		$udl = length $tpdu;
	}
	if ($ud_enc) {
		($ud, $mwis, $port, $wcmp, $ehl, $ra) = tpdu_decode_ud($tpdu, $has_udh, $udl, $ud_enc, $ud_cd);
	}
	if (defined $mwi and defined $mwis) {
		foreach (@{$mwis}) {
			next unless $mwi->[0] == $_->[0];
			undef $mwi;
			last;
		}
		unshift @{$mwis}, $mwi if defined $mwi;
	} elsif (defined $mwi) {
		$mwis = [$mwi];
		undef $mwi;
	}
	return ($mti, $fcs, $scts, $pid, $mc, $ad, $mwis, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud);
}

sub tpdu_decode_command {
	# TODO
}

sub tpdu_encode {
	my ($mti, $mms, $rd, $sr, $rp, $mr, $num, $scts, $dt, $st, $pid, $mc, $ad, $mwi, $vp, $udh, $ud_isbin, $data);
	my $tpdu = '';
	my $is_deliver = $mti == 0;
	my $is_submit = $mti == 1;
	my $is_status = $mti == 2;
	die "TPDU MTI unknown value $mti\n" unless $is_deliver or $is_submit or $is_status;
	my ($vpf, $vpd);
	($vpf, $vpd) = tpdu_encode_vp($vp) if $is_submit;
	my $first = 0;
	$first |= ($mti & 0b00000011);
	$first |= 0b00000100 if not $is_submit and not $mms;
	$first |= 0b00000100 if $is_submit and $rd;
	$first |= ($vpf & 0b11) << 3 if $is_submit;
	$first |= 0b00010000 if $sr;
	$first |= 0b01000000 if defined $udh;
	$first |= 0b10000000 if not $is_submit and $rp;
	$tpdu .= chr($first);
	$tpdu .= chr($mr) if $is_deliver;
	$tpdu .= tpdu_encode_address(@{$num});
	if ($is_status) {
		$tpdu .= tpdu_encode_ts(@{$scts});
		$tpdu .= tpdu_encode_ts(@{$dt});
		$tpdu .= tpdu_encode_st(@{$st});
	}
	$tpdu .= chr($pid);
	my ($dcs, $ud_enc) = tpdu_encode_dcs($mc, $ad, $mwi, $ud_isbin, $data);
	$tpdu .= $dcs;
	$tpdu .= tpdu_encode_ts(@{$scts}) if $is_deliver;
	$tpdu .= $vpd;
	$tpdu .= tpdu_encode_ud($udh, $ud_enc, $data);
	return $tpdu;
}

sub tpdu_encode_deliver {
	my ($mms, $sr, $rp, $num, $scts, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $data) = @_;
	return tpdu_encode(0, $mms, undef, $sr, $rp, undef, $num, $scts, undef, undef, $pid, $mc, $ad, $mwi, undef, $udh, $ud_isbin, $data);
}

sub tpdu_encode_submit {
	my ($rd, $sr, $rp, $mr, $num, $pid, $mc, $ad, $mwi, $vp, $udh, $ud_isbin, $data) = @_;
	return tpdu_encode(1, undef, $rd, $sr, $rp, $mr, $num, undef, undef, undef, $pid, $mc, $ad, $mwi, $vp, $udh, $ud_isbin, $data);
}

sub tpdu_encode_status {
	my ($mms, $sr, $mr, $num, $scts, $dt, $st, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $data) = @_;
	return tpdu_encode(2, $mms, undef, $sr, undef, $mr, $num, $scts, $dt, $st, $pid, $mc, $ad, $mwi, undef, $udh, $ud_isbin, $data);
}

sub tpdu_encode_command {
	# TODO
}

sub tpdu_encode_report {
	my ($is_nack, $mti, $fcs, $scts, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $data) = @_;
	my $tpdu = '';
	$tpdu .= chr($mti);
	$tpdu .= chr($fcs) if $is_nack;
	my $pi = 0;
	$pi |= 0b00000001 if defined $pid;
	$pi |= 0b00000010 if defined $mc;
	$pi |= 0b00000100 if defined $udh or defined $data;
	$tpdu .= chr($pi);
	$tpdu .= tpdu_encode_ts(@{$scts}) if $mti == 1;
	$tpdu .= chr($pid) if defined $pid;
	my ($dcs, $ud_enc);
	($dcs, $ud_enc) = tpdu_encode_dcs($mc, $ad, $mwi, $ud_isbin, $data) if defined $mc or $data;
	$tpdu .= $dcs if defined $dcs;
	$tpdu .= tpdu_encode_ud($udh, $ud_enc, $data) if defined $udh or defined $data;
	return $tpdu;
}

sub tpdu_encode_deliver_report {
	my ($is_nack, $fcs, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $ud) = @_;
	return tpdu_encode_report($is_nack, 0, $fcs, undef, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $ud);
}

sub tpdu_encode_submit_report {
	my ($is_nack, $fcs, $scts, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $ud) = @_;
	return tpdu_encode_report($is_nack, 1, $fcs, $scts, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $ud);
}

sub tpdu_encode_deliver_ack {
	return tpdu_encode_deliver_report(0, undef, undef, undef, undef, undef, undef, undef, undef);
}

sub tpdu_encode_submit_ack {
	my ($scts) = @_;
	return tpdu_encode_submit_report(0, undef, $scts, undef, undef, undef, undef, undef, undef, undef);
}

sub tpdu_encode_deliver_nack {
	my ($fcs) = @_;
	return tpdu_encode_deliver_report(1, $fcs, undef, undef, undef, undef, undef, undef undef);
}

sub tpdu_encode_submit_nack {
	my ($fcs, $scts) = @_;
	return tpdu_encode_submit_report(0, $fcs, $scts, undef, undef, undef, undef, undef, undef, undef);
}

### GSM Short Message Radio Layer ###
# RP-DATA/RPDU:
#   3GPP TS 24.011
#     https://www.3gpp.org/dynareport/24011.htm
#     ETSI TS 124 011 V16.0.0 (2020-07)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=60164
#       https://www.etsi.org/deliver/etsi_ts/124000_124099/124011/16.00.00_60/ts_124011v160000p.pdf
# Called party BCD number:
#   3GPP TS 24.008
#     https://www.3gpp.org/DynaReport/24008.htm
#     ETSI TS 124 008 V16.6.0 (2020-10)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=61572
#       https://www.etsi.org/deliver/etsi_ts/124000_124099/124008/16.06.00_60/ts_124008v160600p.pdf
# Media Type application/vnd.3gpp.sms:
#   https://www.iana.org/assignments/media-types/application/vnd.3gpp.sms
#   3GPP TS 23.140
#     https://www.3gpp.org/dynareport/23140.htm
#     ETSI TS 123 140 V6.16.0 (2009-04)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=30520
#       https://www.etsi.org/deliver/etsi_ts/123100_123199/123140/06.16.00_60/ts_123140v061600p.pdf
#   3GPP TS 24.341
#     https://www.3gpp.org/dynareport/24341.htm
#     ETSI TS 124 341 V16.0.0 (2020-11)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=59632
#       https://www.etsi.org/deliver/etsi_ts/124300_124399/124341/16.00.00_60/ts_124341v160000p.pdf

sub rpdu_decode_address {
	my ($address) = @_;
	return unless length $address >= 1;
	my $address_len = ord(substr $address, 0, 1, '');
	return unless length $address_len <= 11;
	return unless length $address >= $address_len;
	$address_len++;
	return (undef, $address_len) if $address_len == 1;
	my $address_type = ord(substr $address, 0, 1, '');
	my $number_type = ($address_type & 0b01110000) >> 4;
	my $number_plan = ($address_type & 0b00001111);
	my $number_value = join '', map { tpdu_decode_semioctet($_) } split //, substr $address, 0, $address_len-2;
	$number_value = "+$number_value" if $number_type == 0b001 and $number_value =~ /^[1-9][0-9]+$/;
	return ([$number_value, $number_type, $number_plan], $address_len);
}

sub rpdu_encode_address {
	my ($number, $type, $plan) = @_;
	return chr(0) unless defined $number and length $number;
	$type = ($number =~ /^(?:\+|00[1-9][0-9]+$)/) ? 0b001 : 0b000 unless defined $type;
	$plan = ($number =~ /^\+?[0-9]+$/) ? 0b0001 : 0b0000 unless defined $plan;
	$number = $1 if $number =~ /^(?:\+|00)(.*)$/ and $type == 0b001;
	die "RPDU number cannot contain non-numeric characters\n" unless $number =~ /^[0-9*#a-cA-C]*$/;
	die "RPDU number type $type is not in range 0b000 ... 0b111\n" if $type < 0 or $type > 0b111;
	die "RPDU number plan $plan is not in range 0b0000 ... 0b1111\n" if $plan < 0 or $plan > 0b1111;
	my $address = '';
	$address .= chr(0b10000000 | ($type << 4) | $plan);
	$address .= tpdu_encode_semioctet($_) foreach unpack '(A2)*', $number;
	die "RPDU number is too long\n" unless length $address <= 11;
	$address = chr(length $address) . $address;
	return $address;
}

sub rpdu_decode {
	my ($rpdu) = @_;
	return unless length $rpdu >= 2;
	my $mti = ord(substr $rpdu, 0, 1, '') & 0b00000111;
	my $mr = ord(substr $rpdu, 0, 1, '');
	my ($oa, $oa_len) = rpdu_decode_address($rpdu);
	return unless defined $oa_len;
	substr $rpdu, 0, $oa_len, '';
	my ($da, $da_len) = rpdu_decode_address($rpdu);
	return unless defined $da_len;
	substr $rpdu, 0, $da_len, '';
	my $tpdu_len = ord(substr $rpdu, 0, 1, '');
	return unless defined $tpdu_len;
	my $tpdu = substr $rpdu, 0, $tpdu_len, '';
	return ($mti, $mr, $oa, $da, $tpdu);
}

sub rpdu_encode {
	my ($mti, $mr, $oa, $da, $tpdu) = @_;
	my $rpdu = '';
	$rpdu .= chr($mti & 0b00000111);
	$rpdu .= chr($mr);
	$oa = [undef] unless defined $oa;
	$rpdu .= rpdu_encode_address(@{$oa});
	$da = [undef] unless defined $da;
	$rpdu .= rpdu_encode_address(@{$da});
	die "RPDU user data are too long\n" unless length $tpdu <= 233;
	$rpdu .= chr(length $tpdu);
	$rpdu .= $tpdu;
	return $rpdu;
}

### GSM Short Message PDU Mode for AT commands ###
# AT PDU Mode:
#   3GPP TS 27.005
#     https://www.3gpp.org/dynareport/27005.htm
#     ETSI TS 127 005 V16.0.0 (2020-08)
#       https://portal.etsi.org/webapp/workprogram/Report_WorkItem.asp?WKI_ID=60120
#       https://www.etsi.org/deliver/etsi_ts/127000_127099/127005/16.00.00_60/ts_127005v160000p.pdf

sub atpdu_decode {
	my ($payload) = @_;
	my $atpdu = pack 'H*', $payload;
	my ($smsc, $smsc_len) = rpdu_decode_address($atpdu);
	return unless defined $smsc_len;
	substr $atpdu, 0, $smsc_len, '';
	return ($smsc, $atpdu);
}

sub atpdu_encode {
	my ($smsc, $tpdu) = @_;
	$smsc = [undef] unless defined $smsc;
	return unpack 'H*', rpdu_encode_address(@{$smsc}) . $tpdu;
}

#####

sub process_tpdu {
	my ($type, $payload) = @_;
	my ($frag, $mti, $fcs, $mms, $rd, $lp, $sr, $rp, $mr, $num, $scts, $dt, $st, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud);
	if ($type == $smdll_types{DATA}) {
		$frag = tpdu_is_fragmented($payload);
		($mti, $mms, $rd, $lp, $sr, $rp, $mr, $num, $scts, $dt, $st, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud) = tpdu_decode($payload);
	} else {
		($mti, $fcs, $scts, $pid, $mc, $ad, $mwis, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud) = tpdu_decode_report($payload, ($type == $smdll_types{NACK}));
	}
	return ($frag, $mti, $num, $scts, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud);
}

sub process_rpdu {
	my ($payload) = @_;
	my ($mti, $mr, $oa, $da, $tpdu) = rpdu_decode($payload);
	return unless defined $tpdu;
	return (($mti%2 == 0 ? $da : $oa), $tpdu, process_tpdu((($mti == 2 or $mti == 3) ? $smdll_types{ACK} : ($mti == 4 or $mti == 5) ? $smdll_types{NACK} : $smdll_types{DATA}), $tpdu));
}

sub process_atpdu {
	my ($payload) = @_;
	my ($smsc, $tpdu) = atpdu_decode($payload);
	return unless defined $tpdu;
	return ($smsc, $tpdu, process_tpdu($smdll_types{DATA}, $tpdu));
}

#####

sub process_audio_init {
	return {};
}

sub process_audio_finish {
	my ($state) = @_;
	my $smtl_buffer = $state->{smtl_buffer};
	# TODO
}

sub process_audio_sample {
	my ($state, $sample) = @_;
	my $smtl_buffer = $state->{smtl_buffer};
	my ($status, $noext, $type, $payload, $checksum) = smdll_decode($state, $sample);
	return unless defined $status;
	return ($status) unless defined $noext;
	$payload = smtl_decode_data($smtl_buffer, $noext, $type, $payload);
	return ($status, $type) unless defined $payload;
	my @tpdu_data;
	@tpdu_data = process_tpdu($type, $payload) if $type == $smdll_types{ACK} or $type == $smdll_types{NACK} or $type == $smdll_types{DATA};
	return ($status, $type, $payload, @tpdu_data);
}

#####

sub process_audio_sample_receive_mode {
	my ($state, $role, $tpdu_callback, $current_message, $remaining_buffer, $finish, $sample) = @_;
	my ($status, $type, $payload, @tpdu_data) = process_audio_sample($state, $sample);
	return ($finish, $status) unless defined $status and not $finish;
	my @next_message;
	my $next_message_wait_before = 0.5;
	my $next_message_wait_after = 0;
	if ($status == $smdll_decode_error_types{NO_ERROR} and defined $type) {
		$state->{receive_error_count} = 0;
		if ($type == $smdll_types{ERROR}) {
			if (@{$remaining_buffer}) {
				@{$remaining_buffer} = ();
				$next_message_wait_before = 1;
			}
			my $error_code = (defined $payload and length $payload == 1) ? ord($payload) : undef;
			if ($error_code == $smdll_error_types{WRONG_CHECKSUM}) {
				warn localtime . " - Received error wrong checksum\n";
				if ($state->{send_error_count}++ >= 4) {
					warn localtime . " - Failed to retry 4 times\n";
					warn localtime . " - Sending connection released\n";
					@next_message = smdll_encode_rel();
					$next_message_wait_after = 0.1;
					$finish = 1;
				} else {
					warn localtime . " - Retrying to send packet again\n";
				}
				@next_message = @{$current_message} unless @next_message;
			} else {
				warn localtime . ' - Received ' . (defined $error_code ? (sprintf 'error code 0x%02x', $error_code) : 'unknown error') . "\n";
				warn localtime . " - Sending connection released\n";
				@next_message = smdll_encode_rel();
				$next_message_wait_after = 0.1;
				$finish = 1;
			}
		} elsif ($type == $smdll_types{DATA}) {
			$state->{send_error_count} = 0;
			if (not defined $payload) {
				warn localtime . " - Received part of extended SM-DLL data\n";
				warn localtime . " - Sending acknowledge\n";
				@next_message = smdll_encode_ack();
			} else {
				warn localtime . " - Received TPDU data\n";
				my $mti = $tpdu_data[1];
				my @time = localtime(time);
				my $tz = int((timegm(@time) - timelocal(@time)) / 60);
				my $scts = [ 1900+$time[5], 1+$time[4], $time[3], $time[2], $time[1], $time[0], ($tz < 0 ? '-' : ''), int(abs($tz)/60), abs($tz)%60 ];
				if ($role eq 'sc') {
					my ($err, $fcs);
					if (not defined $mti) {
						$fcs = 0xFF; # unspecified error cause
						$err = 'broken TPDU';
					} elsif ($mti != 1) {
						$fcs = 0xB0; # TPDU not supported
						$err = 'unsupported TPDU MTI';
					} else {
						$fcs = $tpdu_callback->($payload, @tpdu_data);
						$err = 'TPDU callback' if defined $fcs;
					}
					if (defined $fcs) {
						my $fcs_str = sprintf "0x%02X", $fcs;
						warn localtime . " - Sending negative acknowledge ($fcs_str) due to $err\n";
						@next_message = smdll_encode_nack(tpdu_encode_submit_nack($fcs, $scts));
					} else {
						warn localtime . " - Sending acknowledge\n";
						@next_message = smdll_encode_ack(tpdu_encode_submit_ack($scts));
					}
				} elsif ($role eq 'te') {
					my ($err, $fcs);
					if (not defined $mti) {
						$fcs = 0xFF; # unspecified error cause
						$err = 'broken TPDU';
					} elsif ($mti == 1) {
						$fcs = 0xB0; # TPDU not supported
						$err = 'unsupported TPDU MTI';
					} else {
						$fcs = $tpdu_callback->($payload, @tpdu_data);
						$err = 'TPDU callback' if defined $fcs;
					}
					if (defined $fcs) {
						my $fcs_str = sprintf "0x%02X", $fcs;
						warn localtime . " - Sending negative acknowledge ($fcs_str) due to $err\n";
						@next_message = smdll_encode_nack(tpdu_encode_deliver_nack($fcs));
					} else {
						warn localtime . " - Sending acknowledge\n";
						@next_message = smdll_encode_ack(tpdu_encode_deliver_ack());
					}
				} else {
					my $fcs = $tpdu_callback->($payload, @tpdu_data);
					my $fcs_str = (defined $fcs) ? (sprintf "0x%02X", $fcs) : undef;
					if (defined $mti and $mti == 1) {
						if (defined $fcs) {
							warn localtime . " - Sending negative acknowledge ($fcs_str) for sc role due to TPDU callback\n";
							@next_message = smdll_encode_nack(tpdu_encode_submit_nack($fcs, $scts));
						} else {
							warn localtime . " - Sending acknowledge for sc role\n";
							@next_message = smdll_encode_ack(tpdu_encode_submit_ack($scts));
						}
					} else {
						if (defined $fcs) {
							warn localtime . " - Sending negative acknowledge ($fcs_str) for te role due to TPDU callback\n";
							@next_message = smdll_encode_nack(tpdu_encode_deliver_nack($fcs));
						} else {
							warn localtime . " - Sending acknowledge for te role\n";
							@next_message = smdll_encode_ack(tpdu_encode_deliver_ack());
						}
					}
				}
			}
		} elsif ($type == $smdll_types{EST}) {
			warn localtime . " - Received connection established\n";
			$state->{send_error_count} = 0;
		} elsif ($type == $smdll_types{REL}) {
			warn localtime . " - Received connection released\n";
			$state->{send_error_count} = 0;
			@{$remaining_buffer} = ();
			$finish = 1;
		} else {
			warn localtime . " - Received unknown SM-DLL message\n";
			warn localtime . " - Sending error unknown type\n";
			$state->{send_error_count} = 0;
			@next_message = smdll_encode_error($smdll_error_types{UNKNOWN_TYPE});
		}
	} else {
		if ($status == $smdll_decode_error_types{WRONG_LENGTH}) {
			warn localtime . " - Received SM-DLL message with wrong length\n";
		} else {
			warn localtime . " - Received broken SM-DLL message\n";
		}
		$state->{send_error_count} = 0;
		if ($state->{receive_error_count}++ >= 4) {
			warn localtime . " - Failed to receive SM-DLL message 4 times\n";
			warn localtime . " - Sending connection released\n";
			@next_message = smdll_encode_rel();
			$next_message_wait_after = 0.1;
		} elsif ($status == $smdll_decode_error_types{WRONG_LENGTH}) {
			warn localtime . " - Sending error wrong length\n";
			@next_message = smdll_encode_error($smdll_error_types{WRONG_LENGTH});
		} else {
			warn localtime . " - Sending error wrong checksum\n";
			@next_message = smdll_encode_error($smdll_error_types{WRONG_CHECKSUM});
		}
	}
	if (@next_message) {
		@{$current_message} = @next_message;
		push @{$remaining_buffer}, (0) x int(8000*$next_message_wait_before), @next_message, (0) x int(8000*$next_message_wait_after);
	}
	return ($finish, $status);
}

sub process_silence_receive_mode {
	my ($state, $role, $current_message, $remaining_buffer, $finish, $established, $silence) = @_;
	return $finish if @{$remaining_buffer} or $finish or $silence < 4;
	my @next_message;
	my $next_message_wait_before = @{$remaining_buffer} ? 0.5 : 0;
	my $next_message_wait_after = 0;
	warn localtime . " - Silence for 4 seconds while waiting for response\n";
	if ($state->{send_error_count}++ >= 4 or $state->{receive_error_count}++ >= 4) {
		warn localtime . " - Failed to send or receive message 4 times\n";
		warn localtime . " - Sending connection released\n";
		@next_message = smdll_encode_rel();
		$next_message_wait_after = 0.1;
		@{$remaining_buffer} = ();
		$finish = 1;
	} elsif (not $established) {
		warn localtime . " - Sending connection established\n";
		@next_message = smdll_encode_est();
	} else {
		warn localtime . " - Sending error wrong checksum\n";
		@next_message = smdll_encode_error($smdll_error_types{WRONG_CHECKSUM});
	}
	if (@next_message) {
		@{$current_message} = @next_message;
		push @{$remaining_buffer}, (0) x int(8000*$next_message_wait_before), @next_message, (0) x int(8000*$next_message_wait_after);
	}
	return $finish;
}

#####

my %nbs_ports = (
	80 => 'WWW Server (HTTP)',
	226 => 'vCARD',
	228 => 'vCALENDAR',
	5501 => 'Compact Business Card',
	5502 => 'Service Card',
	5503 => 'Internet Access Configuration Data',
	5505 => 'Ringing Tone',
	5506 => 'Operator Logo',
	5507 => 'CLI Icon',
	5508 => 'Dynamic Menu Control Protocol',
	5511 => 'Message Access Protocol',
	5512 => 'Simple Email Notification',
	5514 => 'Multipart Message',
	5580 => 'Character-mode WWW Access (TTML)',
);

sub generate_email {
	my ($from, $to, $via, $reply, $number, $time, $scts, $port, $wcmp, $ehl, $ud_isbin, $ud, @rpdus) = @_;

	my $incomplete = ref $ud;

	my $domain = ($via =~ /\@(.+)$/) ? $1 : 'localhost';

	my $from_email = $from;
	if ($from_email !~ /\@/) {
		if ($from_email =~ /^\+?[0-9]+$/) {
			$from_email .= "\@$domain";
		} else {
			$from_email =~ s/([\\"])/\\$1/g;
			$from_email =~ s/[\x00-\x20]+/ /g;
			$from_email = qq("$from_email") if $from_email =~ /[ ()<>\@,;:\\"\/\[\]?=]/;
			$from_email = "$from_email <$from_email\@$domain>";
		}
	}

	my $to_email = $to;
	if ($to_email !~ /\@/) {
		if ($to_email =~ /^\+?[0-9]+$/) {
			$to_email .= "\@$domain";
		} else {
			$to_email =~ s/([\\"])/\\$1/g;
			$to_email =~ s/[\x00-\x20]+/ /g;
			$to_email = qq("$to_email") if $to_email =~ /[ ()<>\@,;:\\"\/\[\]?=]/;
			$to_email = "$to_email <$to_email\@$domain>";
		}
	}

	my @mon_abbrv = qw(NULL Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec);
	my @wday_abbrv = qw(Sun Mon Tue Wed Thu Fri Sat);

	my ($year, $mon, $mday, $hour, $min, $sec, $tz0, $tz1, $tz2, $wday);

	($sec, $min, $hour, $mday, $mon, $year, $wday) = localtime($time);
	$year += 1900;
	$mon += 1;
	my $tz = int((timegm(localtime($time)) - $time) / 60);
	($tz0, $tz1, $tz2) = ((($tz < 0) ? '-' : '+'), int(abs($tz)/60), abs($tz)%60);
	my $date_received_email = sprintf "%3s, %2d %3s %4d %02d:%02d:%02d %s%02d%02d", $wday_abbrv[$wday], $mday, $mon_abbrv[$mon], $year, $hour, $min, $sec, $tz0, $tz1, $tz2;

	($year, $mon, $mday, $hour, $min, $sec, $tz0, $tz1, $tz2) = @{$scts} if defined $scts;
	my $date_email = sprintf "%3s, %2d %3s %4d %02d:%02d:%02d %s%02d%02d", $wday_abbrv[$wday], $mday, $mon_abbrv[$mon], $year, $hour, $min, $sec, $tz0, $tz1, $tz2;
	($sec, $min, $hour, $mday, $mon, $year, $wday) = localtime(timegm($sec, $min, $hour, $mday, $mon-1, $year-1900) - "${tz0}1" * 60 * (60*$tz1 + $tz2));
	$year += 1900;
	$mon += 1;
	my $date_print = sprintf "%04d-%02d-%02d_%02d:%02d:%02d", $year, $mon, $mday, $hour, $min, $sec;

	# TODO
	my $mid_email = "<sms-call-$time\@localhost>";

	my $number_print = $number;
	$number_print =~ s/[\s"\/<>[:^print:]]/_/g;

	my $boundary = md5_hex(join '', map { $_->[1] } @rpdus);

	my $ret = '';

	# TODO
	# perl -MSocket -E 'say scalar gethostbyaddr(inet_aton("1.2.3.4"), AF_INET)'
	# NOTE: $peer_addr_dns_ptr may be omitted
	# "Received: from $sip_contact_user\@$sip_contact_host ($peer_addr_dns_ptr [$peer_addr]) by localhost for $sip_request_user\@$sip_request_host; $date_received_email\n";

	# TODO
	$ret .= "From: $from_email\n";

	# TODO
	$ret .= "To: $to_email\n";

	$ret .= "Date: $date_email\n";
	$ret .= "Subject: SIP SMS\n";
	$ret .= "Message-ID: $mid_email\n";
	$ret .= "MIME-Version: 1.0\n";
	$ret .= "Content-Type: multipart/alternative; boundary=$boundary\n";
	$ret .= "Content-Transfer-Encoding: 8bit\n";
	$ret .= "\n";
	$ret .= "--$boundary\n";

	if ($incomplete) {
		my $max = (sort { $b <=> $a } keys %{$ud})[0];
		my $mimetype = ($ud_isbin or defined $ehl) ? 'application/octet-stream' : 'text/plain; charset=utf-8';
		my $type = $ud_isbin ? 'binary' : 'text';
		my $dis = $ud_isbin ? 'attachment' : undef;
		my $enc = $ud_isbin ? 'base64' : '8bit';

		$ret .= "Content-Type: multipart/mixed; boundary=part$boundary\n";
		$ret .= "Content-Description: Extracted body fragments of incomplete SMS\n";
		$ret .= "Content-Transfer-Encoding: 8bit\n";
		$ret .= "\n";
		foreach (sort { $a <=> $b } keys %{$ud}) {
			next unless defined $ud->{$_};
			my $des = "Extracted $type fragment $_/$max of incomplete SMS body\n";
			$ret .= "--part$boundary\n";
			$ret .= "Content-Type: $mimetype\n";
			$ret .= "Content-Description: $des\n";
			$ret .= "Content-Disposition: $dis\n" if defined $dis;
			$ret .= "Content-Transfer-Encoding: $enc\n";
			$ret .= "\n";
			$ret .= ($enc eq 'base64') ? encode_base64($ud->{$_}) : ($ud->{$_} . "\n");
		}
		$ret .= "--part$boundary--\n";
	} elsif (defined $ehl) {
		my $email = $ud;
		$email = decode('UTF-8', $email) unless $ud_isbin;
		my $header = substr $email, 0, $ehl, '';
		$header = encode('UTF-8', $header) unless $ud_isbin;
		$email = encode('UTF-8', $email) unless $ud_isbin;
		$email = "$header\r\n\r\n$email";
		$email = encode_base64($email) if $ud_isbin;
		my $enc = $ud_isbin ? 'base64' : '8bit';

		$ret .= "Content-Type: message/rfc822\n";
		$ret .= "Content-Description: Extracted SMS email body\n";
		$ret .= "Content-Disposition: inline\n";
		$ret .= "Content-Transfer-Encoding: $enc\n";
		$ret .= "\n";
		$ret .= $email;
		$ret .= "\n";
	} elsif (defined $port or $ud_isbin) {
		my $mimetype = 'application/octet-stream';
		my ($prefix, $suffix);
		if (defined $port) {
			if ($port->[0] == 226) {
				$mimetype = 'text/directory';
				$prefix = 'vcard';
				$suffix = 'vcf';
			} elsif ($port->[0] == 228) {
				$mimetype = 'text/x-vCalendar';
				$prefix = 'vcalendar';
				$suffix = 'vcs';
			} elsif ($port->[0] == 5505) {
				$mimetype = 'application/vnd.nokia.ringing-tone';
				$prefix = 'ringtone';
				$suffix = 'rng';
			} elsif ($port->[0] == 5506 or $port->[0] == 5507) {
				$mimetype = 'image/vnd.nokia.ota-bitmap';
				$prefix = ($port->[0] == 5506) ? 'logo' : 'icon';
				$suffix = 'otb';
			}
		}

		$ret .= "Content-Type: $mimetype\n";
		if (defined $prefix and defined $suffix) {
			$ret .= "Content-Disposition: attachment;\n";
			$ret .= "  filename=\"${prefix}_${date_print}_${number_print}.${suffix}\";\n";
			$ret .= "  modification-date=\"$date_email\"\n";
		}
		if (defined $port and exists $nbs_ports{$port->[0]}) {
			$ret .= "Content-Description: $nbs_ports{$port->[0]}\n";
		}
		$ret .= "Content-Transfer-Encoding: base64\n";
		$ret .= "\n";
		$ret .= encode_base64($ud);
	} else {
		$ret .= "Content-Type: text/plain; charset=utf-8\n";
		$ret .= "Content-Description: Extracted SMS text body\n";
		$ret .= "Content-Transfer-Encoding: 8bit\n";
		$ret .= "\n";
		$ret .= $ud . "\n";
	}

	$ret .= "--$boundary\n";

	if (@rpdus > 1 or $incomplete) {

		my $max = $incomplete ? (sort { $b <=> $a } keys %{$ud})[0] : (scalar @rpdus);

		$ret .= "Content-Type: multipart/mixed; boundary=rpdu$boundary\n";
		$ret .= "Content-Description: Original SMS fragments in RPDU format\n";
		$ret .= "Content-Transfer-Encoding: 8bit\n";
		$ret .= "\n";

		for (0..$#rpdus) {
			my $part = $rpdus[$_]->[0];

			my ($rpdu_date_email, $rpdu_date_print) = ($date_email, $date_print);
			if (defined $rpdus[$_]->[2]) {
				($year, $mon, $mday, $hour, $min, $sec, $tz0, $tz1, $tz2) = @{$rpdus[$_]->[2]};
				$rpdu_date_email = sprintf "%3s, %2d %3s %4d %02d:%02d:%02d %s%02d%02d", $wday_abbrv[$wday], $mday, $mon_abbrv[$mon], $year, $hour, $min, $sec, $tz0, $tz1, $tz2;
				($sec, $min, $hour, $mday, $mon, $year, $wday) = localtime(timegm($sec, $min, $hour, $mday, $mon-1, $year-1900) - "${tz0}1" * 60 * (60*$tz1 + $tz2));
				$year += 1900;
				$mon += 1;
				$rpdu_date_print = sprintf "%04d-%02d-%02d_%02d:%02d:%02d", $year, $mon, $mday, $hour, $min, $sec;
			}

			$ret .= "--rpdu$boundary\n";
			$ret .= "Content-Type: application/vnd.3gpp.sms\n";
			$ret .= "Content-Description: Original SMS fragment $part/$max in RPDU format\n";
			$ret .= "Content-Disposition: attachment;\n";
			$ret .= "  filename=\"sms_${rpdu_date_print}_${number_print}_part${part}.sms\";\n";
			$ret .= "  modification-date=\"$rpdu_date_email\"\n";
			$ret .= "Content-Transfer-Encoding: base64\n";
			$ret .= "\n";
			$ret .= encode_base64($rpdus[$_]->[1]);
		}

		$ret .= "--rpdu$boundary--\n";

	} else {
		my ($rpdu_date_email, $rpdu_date_print) = ($date_email, $date_print);
		if (defined $rpdus[0]->[2]) {
			($year, $mon, $mday, $hour, $min, $sec, $tz0, $tz1, $tz2) = @{$rpdus[0]->[2]};
			$rpdu_date_email = sprintf "%3s, %2d %3s %4d %02d:%02d:%02d %s%02d%02d", $wday_abbrv[$wday], $mday, $mon_abbrv[$mon], $year, $hour, $min, $sec, $tz0, $tz1, $tz2;
			($sec, $min, $hour, $mday, $mon, $year, $wday) = localtime(timegm($sec, $min, $hour, $mday, $mon-1, $year-1900) - "${tz0}1" * 60 * (60*$tz1 + $tz2));
			$year += 1900;
			$mon += 1;
			$rpdu_date_print = sprintf "%04d-%02d-%02d_%02d:%02d:%02d", $year, $mon, $mday, $hour, $min, $sec;
		}

		$ret .= "Content-Type: application/vnd.3gpp.sms\n";
		$ret .= "Content-Description: Original SMS in RPDU format\n";
		$ret .= "Content-Disposition: attachment;\n";
		$ret .= "  filename=\"sms_${rpdu_date_print}_${number_print}.sms\";\n";
		$ret .= "  modification-date=\"$rpdu_date_email\"\n";
		$ret .= "Content-Transfer-Encoding: base64\n";
		$ret .= "\n";
		$ret .= encode_base64($rpdus[0]->[1]);
	}

	$ret .= "--$boundary--\n";

	# TODO: $wcmp

	return $ret;
}

sub format_number {
	my ($address, $country) = @_;
	my ($number, $type) = (defined $address and ref $address) ? @{$address} : ($address);
	if (not defined $type or $type == 0b000) { # Unknown number type
		if (defined $country) {
			my $national = Number::Phone::Lib->new($country, $number);
			if (defined $national) {
				my $string = $national->format();
				$string =~ s/[^0-9+]//g;
				$string =~ s/(?<!^)\+//g;
				return $string if length $string;
			}
		}
		my $international = Number::Phone::Lib->new($number);
		if (defined $international) {
			my $string = $international->format();
			$string =~ s/[^0-9+]//g;
			$string =~ s/(?<!^)\+//g;
			return $string if length $string;
		}
	} elsif (defined $country and defined $type and $type == 0b010) { # National number type
		my $national = Number::Phone::Lib->new($country, $number);
		if (defined $national) {
			my $string = $national->format();
			$string =~ s/[^0-9+]//g;
			$string =~ s/(?<!^)\+//g;
			return $string if length $string;
		}
	}
	return $number;
}

sub number_for_rpdu {
	my ($number) = @_;
	return undef unless defined $number;
	if (ref $number) {
		return $number if (not defined $number->[1] or $number->[1] != 0b101) and length $number->[0] <= 20 and $number->[0] =~ /^[0-9*#a-cA-C]*$/;
	} elsif ($number =~ /^(?:sips?:|tel:)?((?:\+|00)?[0-9]{1,20})(?:@.*)?$/) {
		return [$1];
	}
	return undef;
}

# TODO: remove global variables
my ($send_email_env_to, $send_email_env_from);

# TODO: remove global variables
my $store_to_dir;

sub process_full_message {
	my ($smte, $smsc, $country, $time, $mti, $num, $scts, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud, @tpdus) = @_;

	my $number = format_number($num, $country);
	my $reply = format_number($ra, $country);
	my $via = format_number($smsc, $country);
	my ($from, $to);
	if (defined $mti and $mti == 1) {
		$from = format_number($smte, $country);
		$to = $number;
	} else {
		$from = $number;
		$to = format_number($smte, $country);
	}

	warn localtime . " - Received SMS for $to from $from via $via\n";

	my $rpdu_smte = number_for_rpdu($smte);
	my @rpdus = map { [ $_->[0], rpdu_encode(((defined $mti and $mti == 1) ? (0, 0, $rpdu_smte, number_for_rpdu($_->[2])) : (1, 0, number_for_rpdu($_->[2]), $rpdu_smte)), $_->[1]), $_->[3] ] } @tpdus;

	#warn "EMAIL CONTENT:\n" . generate_email($from, $to, $via, $reply, $number, $time, $scts, $port, $wcmp, $ehl, $ud_isbin, $ud, @rpdus) . "\n";

	# send message via email
	if (defined $send_email_env_to) {
		warn localtime . " - Sending SMS to email address $send_email_env_to\n";
		my $email = generate_email($from, $to, $via, $reply, $number, $time, $scts, $port, $wcmp, $ehl, $ud_isbin, $ud, @rpdus);
		open my $pipe, '|-:raw', '/usr/sbin/sendmail', '-oi', '-oeq', (defined $send_email_env_from ? ('-f', $send_email_env_from) : ()), $send_email_env_to;
		if (not $pipe) {
			warn localtime . " - ERROR: Cannot spawn /usr/sbin/sendmail binary: $!\n";
		} else {
			print $pipe $email;
			close $pipe;
		}
	}
}

# TODO: remove global variables
my $frag_cache;

sub process_frag_message {
	my ($smte, $smsc, $country, $tpdu, $frag, $mti, $num, $scts, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud) = @_;

	my $time = time;

	# store RPDU on disk
	if (defined $store_to_dir) {
		my $scts_time;
		if (defined $scts) {
			my ($year, $mon, $mday, $hour, $min, $sec, $tz0, $tz1, $tz2) = @{$scts};
			$scts_time = timegm($sec, $min, $hour, $mday, $mon-1, $year-1900) - "${tz0}1" * 60 * (60*$tz1 + $tz2);
		} else {
			$scts_time = $time;
		}
		my ($sec, $min, $hour, $mday, $mon, $year) = localtime($scts_time);
		$year += 1900;
		$mon += 1;
		my $date = sprintf "%04d-%02d-%02d_%02d:%02d:%02d", $year, $mon, $mday, $hour, $min, $sec;
		my $number = format_number($num, $country);
		$number =~ s/[\s"\/<>[:^print:]]/_/g;
		my $part = (defined $frag) ? ('_part' . $frag->[4]) : '';
		warn localtime . " - Storing RPDU data to file ${store_to_dir}/sms_${date}_${number}${part}.sms\n";
		open my $fh, '>:raw', "${store_to_dir}/sms_${date}_${number}${part}.sms";
		if (not $fh) {
			warn localtime . " - ERROR: Cannot open file: $!\n";
		} else {
			print $fh rpdu_encode(((defined $mti and $mti == 1) ? (0, 0, number_for_rpdu($smte), number_for_rpdu($smsc)) : (1, 0, number_for_rpdu($smsc), number_for_rpdu($smte))), $tpdu);
			close $fh;
		}
	}

	my @tpdus = ([ 0, $tpdu, $smsc, $scts ]);
	if (defined $frag and defined $frag_cache) {
		my ($frag_mti, $frag_num, $frag_ref, $frag_max, $frag_seq) = @{$frag};
		my $frag_smte = !defined $smte ? '' : ref $smte ? $smte->[0] : $smte;
		$frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref}->{$frag_max}->{$frag_seq} = [ $time, $smte, $smsc, $tpdu, $mti, $num, $scts, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud ];
		$frag_cache->{time} = time;
		my $frags = $frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref}->{$frag_max};
		my @frag_nums = sort { $a <=> $b } keys %{$frags};
		return unless scalar @frag_nums == $frag_max;
		for (1..$frag_max) {
			return unless $frag_nums[$_-1] == $_;
		}
		(undef, $smte, $smsc, undef, $mti, $num, $scts, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, undef) = @{$frags->{1}};
		$ud = join '', map { $frags->{$_}->[18] } @frag_nums;
		$ud = tpdu_decompress_ud($ud) if $ud_cd;
		@tpdus = map { [ $_, $frags->{$_}->[3], $frags->{$_}->[2], $frags->{$_}->[6] ] } @frag_nums;
		delete $frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref}->{$frag_max};
		delete $frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref} unless keys %{$frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref}};
		delete $frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num} unless keys %{$frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}};
		delete $frag_cache->{$frag_smte}->{$frag_mti} unless keys %{$frag_cache->{$frag_smte}->{$frag_mti}};
		delete $frag_cache->{$frag_smte} unless keys %{$frag_cache->{$frag_smte}};
		$frag_cache->{time} = time;
	}

	process_full_message($smte, $smsc, $country, $time, $mti, $num, $scts, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud, @tpdus);
}

sub process_frag_cache {
	my ($frag_cache_expire, $country) = @_;
	my $time_expired_after = ($frag_cache_expire >= 0) ? (time - $frag_cache_expire) : 0;
	foreach my $frag_smte (keys %{$frag_cache}) {
		next unless ref $frag_cache->{$frag_smte};
		foreach my $frag_mti (keys %{$frag_cache->{$frag_smte}}) {
			foreach my $frag_num (keys %{$frag_cache->{$frag_smte}->{$frag_mti}}) {
				foreach my $frag_ref (keys %{$frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}}) {
					foreach my $frag_max (keys %{$frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref}}) {
						my $frags = $frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref}->{$frag_max};
						my ($time) = sort { $b <=> $a } map { $_->[0] } values %{$frags};
						next unless $time > $time_expired_after;
						delete $frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref}->{$frag_max};
						$frag_cache->{time} = time;
						my @frag_nums = sort { $a <=> $b } keys %{$frags};
						my (undef, $smte, $smsc, undef, $mti, $num, $scts, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, undef) = @{$frags->{$frag_nums[0]}};
						my $ud = { map { $_ => $frags->{$_}->[18] } @frag_nums };
						$ud->{$frag_max} = undef unless exists $ud->{$frag_max};
						my @tpdus = map { [ $_, $frags->{$_}->[3], $frags->{$_}->[2], $frags->{$_}->[6] ] } @frag_nums;
						process_full_message($smte, $smsc, $country, $time, $mti, $num, $scts, $pid, $mc, $ad, $mwis, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $ud, @tpdus);
					}
					delete $frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref} unless keys %{$frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}->{$frag_ref}};
				}
				delete $frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num} unless keys %{$frag_cache->{$frag_smte}->{$frag_mti}->{$frag_num}};
			}
			delete $frag_cache->{$frag_smte}->{$frag_mti} unless keys %{$frag_cache->{$frag_smte}->{$frag_mti}};
		}
		delete $frag_cache->{$frag_smte} unless keys %{$frag_cache->{$frag_smte}};
	}
}

#####

my $frag_cache_file_time;
sub store_frag_cache {
	my ($frag_cache_file) = @_;
	return if not defined $frag_cache->{time} or $frag_cache->{time} < $frag_cache_file_time;
	if (eval { store($frag_cache, $frag_cache_file) }) {
		$frag_cache_file_time = time;
	} else {
		warn $@;
	}
}

sub sip_split_name_addr {
	my ($name_addr) = @_;
	return ($2, $1) if $name_addr =~ /^\s*(\S*?)\s*<([^>]*)>\s*$/;
	return ($2, $1) if $name_addr =~ /^\s*(.*?)\s*<([^>]*)>/;
	return ($2, $1) if $name_addr =~ /^\s*(.*?)\s([^>]*)\s*$/;
	return ($name_addr, undef);
}

sub protocol_sip_loop {
	my (%options) = @_;
	my $role = $options{role};
	my $country = $options{country};
	my $frag_cache_file = $options{frag_cache_file};
	my $frag_cache_expire = $options{frag_cache_expire};
	my $sip_number = $options{sip_number};
	my $sip_identity = $options{sip_identity};
	my $sip_accept_uri_re = $options{sip_accept_uri_re};
	my $sip_proto = $options{sip_proto};
	my $sip_listen_addr = $options{sip_listen_addr};
	my $sip_listen_port = $options{sip_listen_port};
	my $sip_public_addr = $options{sip_public_addr};
	my $sip_public_port = $options{sip_public_port};
	my $rtp_listen_addr = $options{rtp_listen_addr};
	my $rtp_listen_min_port = $options{rtp_listen_min_port};
	my $rtp_listen_max_port = $options{rtp_listen_max_port};
	my $rtp_public_addr = $options{rtp_public_addr};
	my $rtp_public_port_offset = $options{rtp_public_port_offset};
	my @rtp_codecs = @{$options{rtp_codecs}};
	my $rtp_ptime = $options{rtp_ptime};

	my $sip_proto_uri = ($sip_proto eq 'tls') ? 'sips' : 'sip';

	my $leg = Net::SIP::Leg->new(proto => $sip_proto, addr => $sip_listen_addr, port => $sip_listen_port);
	die "Error: Cannot create leg at $sip_proto:$sip_listen_addr:$sip_listen_port: $!\n" unless defined $leg;

	my $ua = Net::SIP::Simple->new(from => $sip_identity, legs => [ $leg ]);
	die "Error: Cannot create user agent for $sip_identity: $!\n" unless defined $ua;

	$ua->add_timer(30*60, sub { process_frag_cache($frag_cache_expire, $country) }, 30*60, 'process_frag_cache') if $frag_cache_expire;

	$ua->listen(
		filter => sub {
			my ($from, $request) = @_;
			($from) = sip_hdrval2parts(from => $from);
			my ($from_addr) = sip_split_name_addr($from);
			my ($from_domain, $from_user) = sip_uri2parts($from_addr);
			$from_user = '' unless defined $from_user;
			$from_domain =~ s/:\w+$//;
			my $from_uri = (length $from_user) ? "$from_user\@$from_domain" : $from_domain;
			my $accept = (not defined $sip_accept_uri_re or $from_uri =~ $sip_accept_uri_re) ? 1 : 0;
			warn localtime . " - Incoming call from $from_uri " . ($accept ? 'accepted' : 'filtered') . "\n";
			return $accept;
		},
		cb_create => sub {
			my ($call, $request, $leg, $from) = @_;
			# This is the only callback which provides peer socket address
			$call->{param}->{fsms_peer_addr} = $from->{addr};
			return 1;
		},
		cb_invite => sub {
			my ($call, $request) = @_;
			my ($rtp_port, $rtp_sock, $rtcp_sock) = create_rtp_sockets($rtp_listen_addr, 2, $rtp_listen_min_port, $rtp_listen_max_port);
			$rtp_sock or do { warn localtime . " - Error: Cannot create rtp socket at $rtp_listen_addr: $!\n"; $call->cleanup(); return $request->create_response('503', 'Service Unavailable'); };
			$rtcp_sock or do { warn localtime . " - Error: Cannot create rtcp socket at $rtp_listen_addr: $!\n"; $call->cleanup(); return $request->create_response('503', 'Service Unavailable'); };

			my ($codec, $sdp_addr_peer, $fmt_peer, $ptime_peer);
			my $sdp_peer = $call->{param}->{sdp_peer};
			if ($sdp_peer) {
				my @media_peer = $sdp_peer->get_media();
				foreach my $i (0..$#media_peer) {
					my $m = $media_peer[$i];
					$sdp_addr_peer = $m->{addr};
					next unless $m->{proto} eq 'RTP/AVP';
					next unless $m->{media} eq 'audio';
					my $fmts_peer = $m->{fmt};
					next unless $fmts_peer;
					my $ulaw_fmt_peer = $sdp_peer->name2int('PCMU/8000', $i) || 0;
					my $alaw_fmt_peer = $sdp_peer->name2int('PCMA/8000', $i) || 8;
					($ptime_peer) = map { ($_->[0] eq 'a' and $_->[1] =~ /^ptime:\s*([0-9]+)/) ? $1 : () } @{$m->{lines}};
					foreach (@{$fmts_peer}) {
						if ($_ == $ulaw_fmt_peer and grep { $_ eq 'ulaw' } @rtp_codecs) {
							$codec = 'ulaw';
							$fmt_peer = $ulaw_fmt_peer;
							$ptime_peer = 20 unless $ptime_peer;
							last;
						} elsif ($_ == $alaw_fmt_peer and grep { $_ eq 'alaw' } @rtp_codecs) {
							$codec = 'alaw';
							$fmt_peer = $alaw_fmt_peer;
							$ptime_peer = 20 unless $ptime_peer;
							last;
						}
					}
					last if defined $fmt_peer;
				}
			}

			if (not defined $codec) {
				warn localtime . " - No supported codec\n";
				$call->cleanup();
				return $request->create_response('488', 'Not Acceptable Here');
			}

			my $codec_name = ($codec eq 'alaw') ? 'PCMA/8000' : 'PCMU/8000';
			my $fmt = $fmt_peer;
			my $ptime = ($rtp_ptime eq 'peer') ? $ptime_peer : $rtp_ptime;
			my $sdp_addr = defined $rtp_public_addr ? $rtp_public_addr : laddr4dst($sdp_addr_peer);
			my $contact_addr = defined $sip_public_addr ? $sip_public_addr : laddr4dst($call->{param}->{fsms_peer_addr});

			my $sdp = Net::SIP::SDP->new(
				{
					addr => $sdp_addr,
				},
				{
					media => 'audio',
					proto => 'RTP/AVP',
					port => $rtp_port+$rtp_public_port_offset,
					range => 2,
					fmt => [ $fmt ],
					a => [
						"rtpmap:$fmt $codec_name",
						"ptime:$ptime",
					],
				},
			);
			$call->{param}->{rtp_param} = [ $fmt, int(8000*$ptime/1000), $ptime/1000 ];
			$call->{param}->{sdp} = $sdp;
			$call->{param}->{media_lsocks} = [ [ $rtp_sock, $rtcp_sock ] ];
			$call->{param}->{fsms_codec} = $codec;

			return $request->create_response('200', 'OK', { contact => "$sip_proto_uri:$contact_addr:$sip_public_port" }, $sdp);
		},
		init_media => sub {
			my ($call, $param) = @_;

			my $from = $call->get_peer;
			my ($from_addr, $from_name) = sip_split_name_addr($from);
			my ($from_domain, $from_user) = sip_uri2parts($from_addr);
			$from_name = '' unless defined $from_name;
			$from_user = '' unless defined $from_user;
			$from_domain =~ s/:\w+$//;
			# TODO: somehow encode also from_name
			my $from_uri = (length $from_user) ? "$from_user\@$from_domain" : $from_domain;

			my ($to) = sip_hdrval2parts(to => $call->{ctx}->{to});
			my ($to_addr, $to_name) = sip_split_name_addr($to);
			my ($to_domain, $to_user) = sip_uri2parts($to_addr);
			$to_name = '' unless defined $to_name;
			$to_user = '' unless defined $to_user;
			$to_domain =~ s/:\w+$//;
			# TODO: somehow encode also to_name
			my $to_uri = (length $to_user) ? "$to_user\@$to_domain" : $to_domain;

			$to_uri = $sip_number if defined $sip_number;

			my $codec = $call->{param}->{fsms_codec};
			my $fmt = $call->{param}->{rtp_param}->[0];
			my $buffer_size = $call->{param}->{rtp_param}->[1];
			my $finish = 0;
			my $established = 0;
			my $stop_send_receive = 0;
			my $state = process_audio_init();

			my $hangup = sub {
				warn localtime . " - Hangup\n";
				delete $param->{fsms_hangup};
				my $state = delete $param->{fsms_state};
				my $timer = delete $param->{fsms_timer};
				process_audio_finish($state) if defined $state;
				store_frag_cache($frag_cache_file) if defined $frag_cache_file;
				$timer->cancel() if defined $timer;
				$stop_send_receive = 1;
			};

			my $timer = $call->add_timer(5, sub {
				warn localtime . " - No RTP packet received for 5 seconds\n";
				$hangup->();
				$call->bye();
			});

			my @current_message = smdll_encode_est();
			my @remaining_buffer = ((0) x int(8000*1), @current_message);
			warn localtime . " - Sending connection established\n";

			$param->{fsms_state} = $state;
			$param->{fsms_timer} = $timer;
			$param->{fsms_hangup} = $hangup;

			my $tpdu_callback = sub {
				my ($payload, @tpdu_data) = @_;
				my $mti = $tpdu_data[1];
				my ($smsc, $smte) = ($mti == 1) ? ($to_uri, $from_uri) : ($from_uri, $to_uri);
				process_frag_message($smte, $smsc, $country, $payload, @tpdu_data);
				return;
			};

			my $silence_packets = 0;
			my $send_callback = sub {
				my ($seq, $channel) = @_;
				return if $stop_send_receive;

				$silence_packets = @remaining_buffer ? 0 : $silence_packets+1;
				$finish = process_silence_receive_mode($state, $role, \@current_message, \@remaining_buffer, $finish, $established, $silence_packets*$buffer_size/8000);
				if (not @remaining_buffer and $finish) {
					$hangup->();
					$call->bye();
					return;
				}

				my @send_buffer = splice @remaining_buffer, 0, $buffer_size;
				push @send_buffer, (0) x ($buffer_size-@send_buffer);
				my $send_buffer = pack 'C*', map { ($codec eq 'alaw') ? $alaw_compresstab[$_+32768] : $ulaw_compresstab[$_+32768] } @send_buffer;
				return $send_buffer;
			};

			my $receive_callback = sub {
				my ($payload, $seq, $timestamp, $channel, $mpt) = @_;
				return if $stop_send_receive;

				return unless $mpt == $fmt;

				my @receive_buffer = map { ($codec eq 'alaw') ? $alaw_expandtab[$_] : $ulaw_expandtab[$_] } unpack 'C*', $payload;
				for (@receive_buffer) {
					($finish, my $status) = process_audio_sample_receive_mode($state, $role, $tpdu_callback, \@current_message, \@remaining_buffer, $finish, $_);
					$established = 1 if defined $status;
				}

				$timer->{expire} = 5 + $call->{dispatcher}->{eventloop}->looptime;
				return;
			};

			my $rtp = $call->rtp('media_send_recv', $send_callback, 1, $receive_callback);
			return invoke_callback($rtp, $call, $param);
		},
		recv_bye => sub {
			my ($param) = @_;
			warn localtime . " - Received bye\n";
			$param->{fsms_hangup}->() if exists $param->{fsms_hangup};
		},
		cb_cleanup => sub {
			my ($call) = @_;
			my $param = $call->{param};
			my $hangup = delete $param->{fsms_hangup};
			$hangup->() if defined $hangup;
		},
	);

	my $stop;
	local ($SIG{INT}, $SIG{QUIT}, $SIG{TERM});
	$SIG{INT} = $SIG{QUIT} = $SIG{TERM} = sub { $SIG{INT} = $SIG{QUIT} = $SIG{TERM} = 'DEFAULT'; warn localtime . " - Stopping main loop...\n"; $stop = 1; };
	warn localtime . " - Starting main loop...\n";
	$ua->loop(undef, \$stop);
	$ua->cleanup();
	warn localtime . " - Stopped\n";
}


if (grep { $_ eq '--help' } @ARGV) {
	print <<"EOD";
Usage: $0 [ options ]

SIP F-SMS receiver. Listen for incoming SIP calls,
receive V.23 modulated F-SMS messages and store
them either on disk or send via email.

Options:
  --help                   Show this help
  --protocol=sip           Application protocol: sip (default sip)
  --mode=receive           Application mode: receive (default receive)
  --role=te|sc|dual        Process role: te - Terminal Equipment, sc - Service Center, dual - Dual role based on incoming data (default dual)
  --country=code           Country code for telephone numbers normalization (default none - no normalization)
  --frag-cache=loc,expire  Parts of fragmented messages can be stored either persistant disk file or only in process memory (string "mem") or disabled (string "none"). Incomplete parts expire after specified time (in minutes) and/or at process exit (string "atexit"). Default "mem,1440,atexit"
  --sip-number=number      SIP number (default extracted from incoming call SIP To: header)
  --sip-identity=identity  SIP identity (default "F-SMS <sip:fsms\@localhost>")
  --sip-accept-uri=regex   Perl regex with SIP URIs for incoming calls (default ^.*\$)
  --sip-listen=format      format: proto:listen_addr:listen_port/public_addr:public_port (default proto=udp listen_addr=0.0.0.0 listen_port=default_for_proto public_addr=listen_addr public_port=listen_port)
  --rtp-listen=format      format: listen_addr:listen_min_port-listen_max_port/public_addr:public_min_port (default address is sip-listen with whole port range)
  --rtp-codecs=codecs      List of allowed codecs separated by comma, chosen codec is by peer preference (default ulaw,alaw)
  --rtp-ptime=ptime        Request receiving RTP packet length in milliseconds (default same length as peer requested from us)
  --store-to-dir=dir       Specify disk directory where to store received messages in RPDU format (application/vnd.3gpp.sms)
  --send-email=to,from     Specify envelope to recipient and optional from address (default from address is current user)

Is is required to specify at least --store-to or --send-email option.
EOD
	exit 1;
}

my %options;
foreach (@ARGV) {
	die "$0: Invalid argument $_\n" unless $_ =~ /^--([^=]+)=(.*)$/;
	die "$0: Option --$1 was already specified\n" if exists $options{$1};
	$options{$1} = $2;
}

my $protocol = exists $options{protocol} ? delete $options{protocol} : 'sip';
die "$0: Unknown protocol $protocol\n" unless $protocol eq 'sip';

my $mode = exists $options{mode} ? delete $options{mode} : 'receive';
die "$0: Unknown mode $mode\n" unless $mode eq 'receive';

my $role = exists $options{role} ? delete $options{role} : 'dual';
die "$0: Unknown role $role\n" unless $role =~ /^(?:te|sc|dual)$/;

my $country = exists $options{country} ? delete $options{country} : undef;
if (defined $country) {
	# This same logic as Number::Phone::Lib->new is using
	my $check;
	if ($country =~ /[a-z]/i) {
		$check = country_code($country);
	} else {
		my $check_input = $country;
		$check_input =~ s/[^+0-9]//g;
		$check_input = "+$check_input" if $check_input !~ /^\+/;
		$check = phone2country($check_input);
	}
	die "$0: Invalid country code $country\n" unless defined $check;
}

my $frag_cache_opt = exists $options{'frag-cache'} ? delete $options{'frag-cache'} : 'mem';
die "$0: Invalid --frag-cache option $frag_cache_opt\n" unless $frag_cache_opt =~ /^(.*?|mem|none)(?:,([0-9]+))?(,atexit)?$/ and not ($1 eq 'none' and (defined $2 or defined $3));
my $frag_cache_file = ($1 ne 'mem' and $1 ne 'none') ? $1 : undef;
my $frag_cache_expire = (defined $2) ? $2 : 1440;
my $frag_cache_disabled = ($1 eq 'none');
my $frag_cache_expire_atexit = (defined $3 or $1 eq 'mem');

my $sip_listen = exists $options{'sip-listen'} ? delete $options{'sip-listen'} : '';
die "$0: Invalid --sip-listen option $sip_listen\n" unless $sip_listen =~ /^(?:(tcp|udp|tls):)?([^\[\]<>:]*|\[[^\[\]<>]*\])(?::([0-9]+))?(?:\/([^\[\]<>:]*|\[[^\[\]<>]*\])(?::([0-9]+))?)?$/;
my $sip_proto = (defined $1) ? $1 : 'udp';
my $sip_listen_addr = (length $2) ? $2 : '0.0.0.0';
my $sip_listen_port = (defined $3) ? $3 : ($sip_proto eq 'tls') ? 5061 : 5060;
my $sip_public_addr = (defined $4) ? $4 : $sip_listen_addr;
$sip_public_addr = undef if ip_canonical($sip_public_addr) =~ /^(?:0.0.0.0|::)$/;
my $sip_public_port = (defined $5) ? $5 : $sip_listen_port;

my $sip_number = exists $options{'sip-number'} ? delete $options{'sip-number'} : undef;
my $sip_identity = exists $options{'sip-identity'} ? delete $options{'sip-identity'} : ('F-SMS <' . (($sip_proto eq 'tls') ? 'sips' : 'sip') . ':fsms@localhost>');
my $sip_accept_uri_re = exists $options{'sip-accept-uri'} ? delete $options{'sip-accept-uri'} : undef;
$sip_accept_uri_re = qr/$sip_accept_uri_re/ if defined $sip_accept_uri_re;

my $rtp_listen = exists $options{'rtp-listen'} ? delete $options{'rtp-listen'} : $sip_listen_addr;
die "$0: Invalid --rtp-listen option $rtp_listen\n" unless $rtp_listen =~ /^([^\[\]<>:]*|\[[^\[\]<>]*\])(?::([0-9]+)-([0-9]+))?(?:\/([^\[\]<>:]*|\[[^\[\]<>]*\])(?::([0-9]+))?)?$/;
my $rtp_listen_addr = (length $1) ? $1 : $sip_listen_addr;
my $rtp_listen_min_port = (defined $2) ? $2 : $Net::SIP::Util::RTP_MIN_PORT;
my $rtp_listen_max_port = (defined $3) ? $3 : $Net::SIP::Util::RTP_MAX_PORT;
die "$0: Invalid RTP listen max port $rtp_listen_max_port\n" if $rtp_listen_max_port < $rtp_listen_min_port+1 or $rtp_listen_max_port >= 2**16;
my $rtp_public_addr = (defined $4) ? $4 : $rtp_listen_addr;
$rtp_public_addr = undef if ip_canonical($rtp_public_addr) =~ /^(?:0.0.0.0|::)$/;
my $rtp_public_port_offset = (defined $5) ? ($5-$rtp_listen_min_port) : 0;
die "$0: Invalid RTP public min port $5\n" if $rtp_listen_max_port+$rtp_public_port_offset >= 2**16;

my @rtp_codecs = exists $options{'rtp-codecs'} ? (split /,/, $options{'rtp-codecs'}) : qw(ulaw alaw);
die "$0: Invalid RTP codec $_\n" foreach grep { $_ !~ /^(?:ulaw|alaw)$/ } @rtp_codecs;
my $rtp_ptime = exists $options{'rtp-ptime'} ? $options{'rtp-ptime'} : 'peer';
die "$0: Invalid RTP ptime $rtp_ptime\n" unless $rtp_ptime =~ /^(?:[0-9]+|peer)$/;

$store_to_dir = delete $options{'store-to-dir'} if exists $options{'store-to-dir'};
die "$0: Directory $store_to_dir does not exist\n" if defined $store_to_dir and not -d $store_to_dir;

my $send_email = exists $options{'send-email'} ? delete $options{'send-email'} : undef;
if (defined $send_email) {
	die "$0: Invalid --send-email option $send_email\n" unless $send_email =~ /^([^,]+)(?:,([^,]+))?$/;
	$send_email_env_to = $1;
	$send_email_env_from = $2;
}

my ($extra_key) = sort keys %options;
die "$0: Unknown option --$extra_key\n" if defined $extra_key;

if (defined $frag_cache_file) {
	if (-e $frag_cache_file) {
		$frag_cache = retrieve($frag_cache_file);
		die "$0: Cache file $frag_cache_file is in incompatible format\n" unless defined $frag_cache and ref $frag_cache eq 'HASH';
	} else {
		$frag_cache = {};
	}
	store($frag_cache, $frag_cache_file);
	$frag_cache_file_time = time;
} elsif (not $frag_cache_disabled) {
	$frag_cache = {};
}

protocol_sip_loop(
	role => $role,
	country => $country,
	frag_cache_file => $frag_cache_file,
	frag_cache_expire => $frag_cache_expire,
	sip_number => $sip_number,
	sip_identity => $sip_identity,
	sip_accept_uri_re => $sip_accept_uri_re,
	sip_proto => $sip_proto,
	sip_listen_addr => $sip_listen_addr,
	sip_listen_port => $sip_listen_port,
	sip_public_addr => $sip_public_addr,
	sip_public_port => $sip_public_port,
	rtp_listen_addr => $rtp_listen_addr,
	rtp_listen_min_port => $rtp_listen_min_port,
	rtp_listen_max_port => $rtp_listen_max_port,
	rtp_public_addr => $rtp_public_addr,
	rtp_public_port_offset => $rtp_public_port_offset,
	rtp_codecs => \@rtp_codecs,
	rtp_ptime => $rtp_ptime,
);

process_frag_cache(-1, $country) if $frag_cache_expire_atexit;
store_frag_cache($frag_cache_file) if defined $frag_cache_file;
