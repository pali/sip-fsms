#!/usr/bin/perl
# (c) Pali 2020-2021, Perl license

use strict;
use warnings;

use Encode qw(decode encode);
use Digest::MD5 qw(md5_hex);
use MIME::Base64 qw(encode_base64);
use Scalar::Util qw(refaddr weaken);
use Storable qw(retrieve store);
use Time::Local qw(timegm timelocal);

use Net::SIP 0.816 qw(create_rtp_sockets hostname2ip INETSOCK invoke_callback ip_canonical ip_parts2sockaddr ip_sockaddr2parts ip_string2parts laddr4dst sip_hdrval2parts sip_uri2parts);
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
	push @samples, v23_encode($phase, $baud_pll, 0);
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
		my $ignore_lost = $state->{ignore_lost};
		my $had_signal = $state->{had_signal};
		$state->{ignore_lost} = 0;
		$state->{had_signal} = 0;
		$state->{mark_bits} = 0;
		$state->{had_mark_signal} = 0;
		return ($had_signal and not $ignore_lost) ? $smdll_decode_error_types{LOST_SIGNAL} : ();
	} elsif (not $state->{had_signal}) {
		$state->{ignore_lost} = 0;
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
		my $ignore_lost = $state->{ignore_lost};
		$state->{ignore_lost} = 1;
		$state->{mark_bits} = 0;
		$state->{had_mark_signal} = 0;
		$state->{skip_mark_bits} = 0;
		return ($had_carrier and not $ignore_lost) ? $smdll_decode_error_types{LOST_CARRIER} : ();
	} elsif (not $had_carrier) {
		$state->{ignore_lost} = 0;
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
			$state->{ignore_lost} = 1;
			$state->{mark_bits} = 0;
			$state->{had_mark_signal} = 0;
			$state->{smdll_buffer} = [];
			return $smdll_decode_error_types{BROKEN_STOP_BIT};
		}
		push @{$state->{smdll_buffer}}, ord(pack('b*', join '', @{$state->{smdll_bits}}[1..8]));
		$state->{smdll_bits} = [];
	} else {
		if (@{$state->{smdll_bits}} == 0 and $newbit != 0) {
			$state->{ignore_lost} = 1;
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
	$state->{ignore_lost} = 1;
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
	my @payloads = defined $tpdu ? unpack('(a176)*', $tpdu) : ();
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
	return encode('UTF-8', decode('GSM0338', substr(pack('(b*)*', unpack '(a7)*', unpack 'b*', $_[0]), 0, $_[1])));
}

sub tpdu_encode_7bit {
	my $bytes = encode('GSM0338', decode('UTF-8', $_[0]));
	my $len = length $bytes;
	my $septets = pack 'b*', join '', map { substr $_, 0, 7 } unpack '(a8)*', unpack 'b*', $bytes;
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
	my $first = ord(substr $address_value, 0, 1);
	$first = (($first & 0b00001111) << 4) | (($first & 0b11110000) >> 4);
	my $number_value;
	if ($number_type == 0b101) {
		$number_value = tpdu_decode_7bit($address_value, $address_len-2);
	} elsif ($number_type == 0b000 and $number_plan == 0b1001 and ($first & 0b11100000) == 0b00000000 and ($first & 0b00011111) == $number_len-2) {
		# Special undocumented GSM 7bit encoding for F-SMS TPDU address used in Czech Republic:
		# Bytes are encoded as semioctets, first encoded byte has upper 3 bits unset,
		# lower 5 bits of first byte represents number of following semioctets
		# and the rest encoded bytes contain GSM 7bit septets packed as bytes.
		$address_value = join '', map { chr(((ord($_) & 0b00001111) << 4) | ((ord($_) & 0b11110000) >> 4)) } split //, $address_value;
		# one semioctet is 4 bits long, one septet is 7 bits long
		my $septets_len = int(ord(substr $address_value, 0, 1, '') * 4 / 7);
		$septets_len = $address_len-2 if $septets_len > $address_len-2;
		$number_value = tpdu_decode_7bit($address_value, $septets_len);
		$number_type = 0b101;
	} elsif ($number_type == 0b000 and $number_plan == 0b1001) {
		# Special undocumented Alphabet encoding for F-SMS TPDU address used in Czech Republic:
		# Characters are encoded as semioctets indexed from one: A=1, B=2, ... N=14, O=15, P=0.
		# And then it overflows and continues again from one: Q=1, R=2, S=3, ... Y=9, Z=10.
		# Because decoding of 1..10 is ambiguous, decode all semioctets as A-P characters only.
		$number_value = substr(join('', map { chr(ord("A") + ($_ + 16 - 1) % 16) } map { (ord($_) & 0b1111), (ord($_) >> 4) } split //, $address_value), 0, $number_len);
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
		$address .= tpdu_encode_semioctet($_) foreach unpack '(a2)*', $number;
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
	$ts .= tpdu_encode_semioctet($_) foreach unpack '(a2)*', join '', map { sprintf '%02u', $_ } @ts;
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
	my ($mc, $ad, $mwi, $ud_isbin, $ud_cd, $data, $ud_ucs2) = @_;
	die "TPDU message class is invalid\n" if defined $mc and ($mc < 0 or $mc > 3);
	die "TPDU message class and message waiting indicator cannot be used together\n" if defined $mc and defined $mwi;
	die "TPDU binary data cannot contain wide characters\n" if $ud_isbin and $data =~ /[^\x00-\xff]/;
	my $ud_enc = $ud_isbin ? 1 : (defined $ud_ucs2) ? ($ud_ucs2 ? 2 : 0) : eval { encode('GSM0338', decode('UTF-8', $data), 1); 1 } ? 0 : 2;
	my $dcs = 0;
	if (defined $mwi) {
		$dcs |= 0b11000000;
		$dcs |= ($mwi->[0] & 0b11);
		$dcs |= 0b00001000 if $mwi->[1];
		die "TPDU message waiting indicator cannot be used with binary data\n" if $ud_enc == 1;
		die "TPDU message waiting indicator cannot be used together with compression\n" if $ud_cd;
		die "TPDU message waiting indicator and automatic deletion cannot be used with UCS-2 data\n" if $ad and $ud_enc == 2;
		$dcs |= ($ud_enc == 2 ? 0b00100000 : 0b00010000) unless $ad;
	} else {
		if (defined $mc) {
			$dcs |= 0b00010000;
			$dcs |= $mc;
		}
		$dcs |= 0b01000000 if $ad;
		$dcs |= 0b00100000 if $ud_cd;
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
	my $sr = ($first & 0b00100000) ? 1 : 0;
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
	# TODO: change $mwi to $mwis
	my ($mti, $mms, $rd, $lp, $sr, $rp, $mr, $num, $scts, $dt, $st, $pid, $mc, $ad, $mwi, $vp, $port, $wcmp, $ehl, $ra, $ud_isbin, $ud_cd, $data, $ud_ucs2, $udh) = @_;
	my $tpdu = '';
	my $is_deliver = $mti == 0;
	my $is_submit = $mti == 1;
	my $is_status = $mti == 2;
	die "TPDU MTI unknown value $mti\n" unless $is_deliver or $is_submit or $is_status;
	my ($vpf, $vpd);
	($vpf, $vpd) = tpdu_encode_vp(defined $vp ? @{$vp} : ()) if $is_submit;
	my $first = 0;
	$first |= ($mti & 0b00000011);
	$first |= 0b00000100 if not $is_submit and not $mms;
	$first |= 0b00000100 if $is_submit and $rd;
	$first |= ($vpf & 0b11) << 3 if $is_submit;
	$first |= 0b00001000 if not $is_submit and $lp;
	$first |= 0b00100000 if $sr;
	$first |= 0b01000000 if defined $udh;
	$first |= 0b10000000 if not $is_submit and $rp;
	$tpdu .= chr($first);
	$tpdu .= chr($mr || 0) unless $is_deliver;
	$tpdu .= tpdu_encode_address(ref $num ? @{$num} : $num);
	if ($is_status) {
		$tpdu .= tpdu_encode_ts(@{$scts});
		$tpdu .= tpdu_encode_ts(@{$dt});
		$tpdu .= tpdu_encode_st(@{$st});
	}
	$tpdu .= chr($pid);
	my ($dcs, $ud_enc) = tpdu_encode_dcs($mc, $ad, $mwi, $ud_isbin, $ud_cd, $data, $ud_ucs2);
	$tpdu .= $dcs;
	$tpdu .= tpdu_encode_ts(@{$scts}) if $is_deliver;
	$tpdu .= $vpd if $is_submit;
	$tpdu .= tpdu_encode_ud($udh, $ud_enc, $data);
	return $tpdu;
}

sub tpdu_encode_deliver {
	my ($mms, $lp, $sr, $rp, $num, $scts, $pid, $mc, $ad, $mwi, $ud_isbin, $ud_cd, $data, $ud_ucs2, $udh) = @_;
	return tpdu_encode(0, $mms, undef, $lp, $sr, $rp, undef, $num, $scts, undef, undef, $pid, $mc, $ad, $mwi, undef, undef, undef, undef, undef, $ud_isbin, $ud_cd, $data, $ud_ucs2, $udh);
}

sub tpdu_encode_submit {
	my ($rd, $sr, $rp, $mr, $num, $pid, $mc, $ad, $mwi, $vp, $ud_isbin, $ud_cd, $data, $ud_ucs2, $udh) = @_;
	return tpdu_encode(1, undef, $rd, undef, $sr, $rp, $mr, $num, undef, undef, undef, $pid, $mc, $ad, $mwi, $vp, undef, undef, undef, undef, $ud_isbin, $ud_cd, $data, $ud_ucs2, $udh);
}

sub tpdu_encode_status {
	my ($mms, $sr, $mr, $num, $scts, $dt, $st, $pid, $mc, $ad, $mwi, $ud_isbin, $ud_cd, $data, $ud_ucs2, $udh) = @_;
	return tpdu_encode(2, $mms, undef, undef, $sr, undef, $mr, $num, $scts, $dt, $st, $pid, $mc, $ad, $mwi, undef, undef, undef, undef, undef, $ud_isbin, $ud_cd, $data, $ud_ucs2, $udh);
}

sub tpdu_encode_command {
	# TODO
}

sub tpdu_encode_report {
	my ($is_nack, $mti, $fcs, $scts, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $ud_cd, $data, $ud_ucs2) = @_;
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
	($dcs, $ud_enc) = tpdu_encode_dcs($mc, $ad, $mwi, $ud_isbin, $ud_cd, $data, $ud_ucs2) if defined $mc or $data;
	$tpdu .= $dcs if defined $dcs;
	$tpdu .= tpdu_encode_ud($udh, $ud_enc, $data) if defined $udh or defined $data;
	return $tpdu;
}

sub tpdu_encode_deliver_report {
	my ($is_nack, $fcs, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $ud_cd, $ud) = @_;
	return tpdu_encode_report($is_nack, 0, $fcs, undef, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $ud_cd, $ud);
}

sub tpdu_encode_submit_report {
	my ($is_nack, $fcs, $scts, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $ud_cd, $ud) = @_;
	return tpdu_encode_report($is_nack, 1, $fcs, $scts, $pid, $mc, $ad, $mwi, $udh, $ud_isbin, $ud_cd, $ud);
}

sub tpdu_encode_deliver_ack {
	return tpdu_encode_deliver_report(0, undef, undef, undef, undef, undef, undef, undef, undef, undef);
}

sub tpdu_encode_submit_ack {
	my ($scts) = @_;
	return tpdu_encode_submit_report(0, undef, $scts, undef, undef, undef, undef, undef, undef, undef, undef);
}

sub tpdu_encode_deliver_nack {
	my ($fcs) = @_;
	return tpdu_encode_deliver_report(1, $fcs, undef, undef, undef, undef, undef, undef, undef, undef);
}

sub tpdu_encode_submit_nack {
	my ($fcs, $scts) = @_;
	return tpdu_encode_submit_report(0, $fcs, $scts, undef, undef, undef, undef, undef, undef, undef, undef);
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
	$address .= tpdu_encode_semioctet($_) foreach unpack '(a2)*', $number;
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

sub decode_audio_sample {
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

sub prepare_data_messages_send_mode {
	my ($state, $finish, $tpdu) = @_;
	my @next_message;
	my $next_message_wait_after = 0;
	delete $state->{send_data_messages};
	my @data_messages = (defined $tpdu) ? smtl_encode_data($tpdu) : ();
	if (@data_messages) {
		my $next_message = shift @data_messages;
		@next_message = @{$next_message};
		$state->{send_data_messages} = [ @data_messages ] if @data_messages;
		if (@data_messages) {
			warn localtime . " - Sending part of extended SM-DLL data\n";
		} else {
			warn localtime . " - Sending TPDU data\n";
		}
	} else {
		warn localtime . " - No more messages to send\n";
		warn localtime . " - Sending connection released\n";
		@next_message = smdll_encode_rel();
		$next_message_wait_after = 0.1;
		$finish = 1;
	}
	return ($finish, $next_message_wait_after, @next_message);
}

sub process_audio_sample {
	my ($state, $mode, $role, $tpdu_callback, $current_message, $remaining_buffer, $finish, $sample) = @_;
	my ($status, $type, $payload, @tpdu_data) = decode_audio_sample($state, $sample);
	return ($finish, $status) unless defined $status and not $finish;
	my @next_message;
	my $next_message_prepend_only = 0;
	my $next_message_wait_before = 0.2;
	my $next_message_wait_after = 0;
	if ($status == $smdll_decode_error_types{NO_ERROR} and defined $type) {
		$state->{receive_error_count} = 0;
		if ($type == $smdll_types{ERROR}) {
			if (@{$remaining_buffer}) {
				@{$remaining_buffer} = ();
				$next_message_wait_before = 1;
			}
			my $error_code = (defined $payload and length $payload == 1) ? ord($payload) : undef;
			if ($mode eq 'send' and defined $error_code and $error_code == $smdll_error_types{UNSUPP_EXT} and exists $state->{send_data_messages} and @{$state->{send_data_messages}}) {
				warn localtime . " - Received error extension mechanism not supported\n";
				my $tpdu = $tpdu_callback->(1, $smdll_types{ERROR});
				($finish, $next_message_wait_after, @next_message) = prepare_data_messages_send_mode($state, $finish, $tpdu);
			} elsif ($mode eq 'receive' or (defined $error_code and $error_code == $smdll_error_types{WRONG_CHECKSUM})) {
				warn localtime . ' - Received ' . (defined $error_code ? ($error_code == $smdll_error_types{WRONG_CHECKSUM} ? 'error wrong checksum' : (sprintf 'error code 0x%02x', $error_code)) : 'unknown error') . "\n";
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
		} elsif ($mode eq 'receive' and $type == $smdll_types{DATA}) {
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
						$fcs = $tpdu_callback->(1, $type, $payload, @tpdu_data);
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
						$fcs = $tpdu_callback->(1, $type, $payload, @tpdu_data);
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
					my $fcs = $tpdu_callback->(1, $type, $payload, @tpdu_data);
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
		} elsif ($mode eq 'send' and ($type == $smdll_types{ACK} or $type == $smdll_types{NACK})) {
			$state->{send_error_count} = 0;
			my $no_error = not @{$remaining_buffer}; # no_error if message was fully send
			if (not defined $payload and exists $state->{send_data_messages} and @{$state->{send_data_messages}}) {
				if ($type == $smdll_types{NACK}) {
					warn localtime . " - Received negative acknowledge for part of extended SM-DLL data\n";
					my $tpdu = $tpdu_callback->($no_error, $smdll_types{ERROR});
					($finish, $next_message_wait_after, @next_message) = prepare_data_messages_send_mode($state, $finish, $tpdu);
				} else {
					warn localtime . " - Received acknowledge for part of extended SM-DLL data\n";
					my $next_message = shift @{$state->{send_data_messages}};
					@next_message = @{$next_message};
					if (@{$state->{send_data_messages}}) {
						warn localtime . " - Sending part of extended SM-DLL data\n";
					} else {
						warn localtime . " - Sending TPDU data\n";
						delete $state->{send_data_messages};
					}
				}
			} else {
				if ($type == $smdll_types{NACK}) {
					warn localtime . " - Received negative acknowledge\n";
				} else {
					warn localtime . " - Received acknowledge\n";
				}
				my $tpdu = $tpdu_callback->($no_error, $type, $payload, @tpdu_data);
				($finish, $next_message_wait_after, @next_message) = prepare_data_messages_send_mode($state, $finish, $tpdu);
			}
		} elsif ($mode eq 'send' and $type == $smdll_types{EST}) {
			warn localtime . " - Received connection established\n";
			$state->{send_error_count} = 0;
			my $tpdu = $tpdu_callback->(1, undef);
			($finish, $next_message_wait_after, @next_message) = prepare_data_messages_send_mode($state, $finish, $tpdu);
		} elsif ($type == $smdll_types{REL}) {
			warn localtime . " - Received connection released\n";
			$state->{send_error_count} = 0;
			@{$remaining_buffer} = ();
			$finish = 1;
		} else {
			warn localtime . " - Received unknown SM-DLL message " . (sprintf '0x%02x', $type) . "\n";
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
			$next_message_prepend_only = 1;
		}
	}
	if (@next_message) {
		@{$current_message} = @next_message unless $next_message_prepend_only;
		push @{$remaining_buffer}, (0) x int(8000*$next_message_wait_before), @next_message, (0) x int(8000*$next_message_wait_after);
	}
	return ($finish, $status);
}

sub process_timeout {
	my ($state, $mode, $role, $current_message, $remaining_buffer, $finish, $established, $timeout) = @_;
	return $finish if @{$remaining_buffer} or $finish or $timeout < 4;
	my @next_message;
	my $next_message_prepend_only = 0;
	my $next_message_wait_before = @{$remaining_buffer} ? 0.2 : 0;
	my $next_message_wait_after = 0;
	warn localtime . " - 4 seconds timeout while waiting for response\n";
	if ($state->{send_error_count}++ >= 4 or $state->{receive_error_count}++ >= 4) {
		warn localtime . " - Failed to send or receive message 4 times\n";
		warn localtime . " - Sending connection released\n";
		@next_message = smdll_encode_rel();
		$next_message_wait_after = 0.1;
		@{$remaining_buffer} = ();
		$finish = 1;
	} elsif (not $established and $mode eq 'receive') {
		warn localtime . " - Sending connection established\n";
		@next_message = smdll_encode_est();
	} else {
		warn localtime . " - Sending error wrong checksum\n";
		@next_message = smdll_encode_error($smdll_error_types{WRONG_CHECKSUM});
		$next_message_prepend_only = 1;
	}
	if (@next_message) {
		@{$current_message} = @next_message unless $next_message_prepend_only;
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
	} elsif ($number =~ /^(?:sips?:|tel:)?(\+|00(?=[1-9][0-9]))?([-.()0-9*#a-cA-C]+)(?:\@[^;]*)?((?:;[^=]+=[^;]+)+)?$/) {
		my $prefix = $1;
		my $suffix = $3;
		$number = $2;
		if (not defined $prefix and defined $suffix and $suffix =~ /;phone-context=(\+|00(?=[1-9][0-9]))?([-.()0-9*#a-cA-C]+)(?:;|$)/) {
			$prefix = $1;
			$number = $2 . $number;
		}
		$number =~ s/[-.()]//g;
		$prefix = '' unless defined $prefix;
		return [ $prefix . $number ] if length $number > 0 and length $number <= 20;
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

	$from = 'unknown' unless defined $from;
	$to = 'unknown' unless defined $to;
	$via = 'unknown' unless defined $via;

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
		my $dup = 0;
		my $dupstr = '';
		while (-e "${store_to_dir}/sms_${date}_${number}${part}${dupstr}.sms") {
			$dup++;
			$dupstr = "_dup$dup";
		}
		warn localtime . " - Storing RPDU data to file ${store_to_dir}/sms_${date}_${number}${part}${dupstr}.sms\n";
		open my $fh, '>:raw', "${store_to_dir}/sms_${date}_${number}${part}${dupstr}.sms";
		if (not $fh) {
			warn localtime . " - ERROR: Cannot create file: $!\n";
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

sub ip_addr_is_reserved {
	my ($addr) = @_;
	return ($addr !~ /:/ and ip_canonical($addr) =~ /^(?:0|10|100\.(?:6[4-9]|[7-9][0-9]|1[0-1][0-9]|12[0-7])|169\.254|172\.(?:1[6-9]|2[0-9]|3[0-1])|192\.0\.0|192\.0\.2|192\.31\.196|192\.52\.193|192\.88\.99|192\.168|192\.175\.48|198\.1[8-9]|198\.51\.100|203\.0\.113|22[4-9]|2[3-5][0-9])\./) ? 1 : 0;
}

sub ip_addr_is_invalid {
	my ($addr) = @_;
	return 1 unless defined $addr;
	$addr =~ s/^\[(.*)\]$/$1/;
	return 1 unless length $addr;
	return 1 unless eval { $addr = ip_canonical($addr) };
	return ($addr =~ /^(?:0|22[4-9]|2[3-5][0-9])\./) ? 1 : 0;
}

sub ip_addr_is_wildcard {
	my ($addr) = @_;
	$addr =~ s/^\[(.*)\]$/$1/;
	$addr = ip_canonical($addr);
	return ($addr =~ /^(?:0\.0\.0\.0|::)$/) ? 1 : 0;
}

sub parse_call_identity {
	my ($candidates, $headers) = @_;
	foreach my $candidate (@{$candidates}) {
		return $candidate unless ref $candidate;
		my ($hdr, $what) = @{$candidate};
		next unless exists $headers->{$hdr};
		foreach my $hdr_val (reverse @{$headers->{$hdr}}) {
			my $number;
			if ($what =~ /^(?:name|user|tel)$/) {
				my ($hdr_parts, $hdr_data) = sip_hdrval2parts($hdr => $hdr_val);
				next unless defined $hdr_parts;
				my ($hdr_addr, $hdr_name) = sip_split_name_addr($hdr_parts);
				if ($what eq 'name') {
					$number = $hdr_name;
				} elsif ($what eq 'user') {
					next unless defined $hdr_addr;
					(undef, $number) = sip_uri2parts($hdr_addr);
				} elsif ($what eq 'tel') {
					next unless $hdr_addr =~ /^tel:(.+)$/;
					$number = $1;
					my $prefix = exists $hdr_data->{'phone-context'} ? $hdr_data->{'phone-context'} : undef;
					$number = $prefix . $number if defined $prefix and $prefix =~ /^([-.()0-9*#a-cA-C]+)$/;
				}
			} else {
				($number) = grep { defined($_) } $hdr_val =~ /$what/;
			}
			next unless defined $number;
			$number =~ s/[-.()]//g;
			return $number if length $number and $number =~ /^\+?[0-9*#a-cA-C]+$/;
		}
	}
	return;
}

sub protocol_sip_loop {
	my (%options) = @_;
	my $mode = $options{mode};
	my $role = $options{role};
	my $country = $options{country};

	my @tpdus = ($mode eq 'send') ? @{$options{tpdus}} : ();

	my $frag_cache_file = $options{frag_cache_file};
	my $frag_cache_expire = $options{frag_cache_expire};
	my $local_sc_number = $options{local_sc_number};
	my $local_te_number = $options{local_te_number};
	my $remote_sc_number = $options{remote_sc_number};
	my $remote_te_number = $options{remote_te_number};

	my $sip_from = $options{sip_from};
	my $sip_to = $options{sip_to};

	my $sip_identity = $options{sip_identity};
	my $sip_accept_uri_re = $options{sip_accept_uri_re};

	my $sip_proto = $options{sip_proto};

	my $sip_auth_user = $options{sip_auth_user};
	my $sip_auth_pass = $options{sip_auth_pass};

	my $sip_peer_host = $options{sip_peer_host};
	my $sip_peer_port = $options{sip_peer_port};

	my $sip_register_host = $options{sip_register_host};
	my $sip_register_port = $options{sip_register_port};
	my @sip_register_timeout = ($mode eq 'receive') ? @{$options{sip_register_timeout}} : ();

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

	$sip_identity = $sip_from unless defined $sip_identity;

	my $sock_proto = ($sip_proto eq 'tls') ? 'tcp' : $sip_proto;
	my $sip_proto_uri = ($sip_proto eq 'tls') ? 'sips' : 'sip';

	my $sip_peer_laddr = defined $sip_peer_host ? laddr4dst($sip_peer_host) : undef;
	$sip_peer_laddr = "[$sip_peer_laddr]" if defined $sip_peer_laddr and $sip_peer_laddr =~ /:/;
	$sip_listen_addr = $sip_peer_laddr if not defined $sip_listen_addr and defined $sip_peer_laddr;

	my $sock = INETSOCK(
		Proto => $sock_proto,
		LocalAddr => $sip_listen_addr,
		LocalPort => $sip_listen_port,
		V6Only => 1,
		Reuse => 1,
		ReuseAddr => 1,
		($sock_proto eq 'tcp') ? (
			Listen => 100,
		) : ($mode eq 'send') ? (
			PeerAddr => $sip_peer_host,
			PeerPort => $sip_peer_port,
		) : (),
	);
	die "Error: Cannot create local socket: $!\n" unless defined $sock;
	$sip_listen_addr = $sock->sockhost();
	$sip_listen_addr = "[$sip_listen_addr]" if $sip_listen_addr =~ /:/;
	$sip_listen_port = $sock->sockport();

	my $contact_addr = defined $sip_public_addr ? $sip_public_addr : (defined $sip_peer_laddr and ip_addr_is_wildcard($sip_listen_addr)) ? $sip_peer_laddr : $sip_listen_addr;
	my $contact_port = $sip_public_port ? $sip_public_port : $sip_listen_port;

	my $leg = Net::SIP::Leg->new(proto => $sip_proto, sock => $sock, (defined $sip_peer_host) ? (dst => "$sip_peer_host:$sip_peer_port") : (), contact => "$sip_proto_uri:$contact_addr:$contact_port");
	die "Error: Cannot create leg at $sip_proto:$sip_listen_addr:$sip_listen_port: $!\n" unless defined $leg;

	my $sip_user_agent = "F-SMS $mode (Net::SIP $Net::SIP::VERSION)";
	my $sip_registrar = defined $sip_register_host ? ($sip_proto_uri . ':' . $sip_register_host . ($sip_register_port ? ":$sip_register_port" : '')) : undef;
	my $sip_outgoing_proxy = defined $sip_peer_host ? "$sip_proto_uri:$sip_peer_host:$sip_peer_port" : undef;
	my $sip_auth = defined $sip_auth_user ? [ $sip_auth_user, $sip_auth_pass ] : undef;
	my $ua = Net::SIP::Simple->new(from => $sip_identity, outgoing_proxy => $sip_outgoing_proxy, registrar => $sip_registrar, auth => $sip_auth, legs => [ $leg ], options => { 'user-agent' => $sip_user_agent });
	die "Error: Cannot create user agent for $sip_identity: $!\n" unless defined $ua;

	my $stop;
	my $stopping;
	my %calls;

	my $stop_cb = sub {
		warn localtime . " - Stopping main loop...\n";
		$stop = 1;
	};

	my $registered;
	my $register_contact_addr;
	if (defined $sip_register_host) {
		my $init_registered;
		my $register_timer;
		my $sub_register;
		my $cb_register = sub {
			my ($status, %info) = @_;
			return if $stopping;
			$registered = ($status eq 'OK');
			my $packet = exists $info{packet} ? $info{packet} : undef;
			$register_timer->cancel() if defined $register_timer;
			my $next = $sip_register_timeout[2];
			if ($status eq 'OK') {
				my $expires = $info{expires} || $sip_register_timeout[0];
				$next = ($sip_register_timeout[0] and $sip_register_timeout[0] < $expires) ? $sip_register_timeout[0] : $expires;
				warn localtime . " - Registration to $sip_registrar successful, expires in $expires seconds\n";
			} elsif (exists $info{code} and defined $info{code}) {
				my $msg = defined $packet ? $packet->msg() : '';
				warn localtime . " - Registration to $sip_registrar failed: $info{code} $msg\n";
			} elsif (exists $info{errno} and defined $info{errno} and $info{errno} =~ /^[1-9][0-9]*$/) {
				$! = int($info{errno});
				warn localtime . " - Registration to $sip_registrar failed: $!\n";
			} else {
				my $error = $ua->error();
				warn localtime . " - Registration to $sip_registrar failed: $error\n";
			}
			$init_registered = 1 if not $init_registered and $registered;
			if (not $init_registered) {
				if ($sip_register_timeout[1] == 1) {
					$init_registered = -1;
					return;
				}
				$sip_register_timeout[1]-- if $sip_register_timeout[1] > 1;
			}
			warn localtime . " - Next register in $next seconds\n";
			$next-- if $next > 1;
			$register_timer = $ua->add_timer($next, $sub_register);
		};
		$sub_register = sub {
			return if $stopping;
			$register_timer->cancel() if defined $register_timer;
			$register_timer = $ua->add_timer(60, sub { $cb_register->('FAIL', errno => 110) });
			if (ip_addr_is_wildcard($contact_addr)) {
				my $dst_addr = hostname2ip((ip_string2parts(scalar sip_uri2parts($sip_register_host)))[0], $sock->sockdomain());
				$dst_addr = ($contact_addr =~ /:/) ? '0100::' : '192.0.2.0' unless $dst_addr; # fallback to IPv6 Discard Prefix or IPv4 TEST-NET-1
				$register_contact_addr = laddr4dst($dst_addr);
			}
			$ua->register(expires => $sip_register_timeout[0], cb_final => $cb_register, ($register_contact_addr ? (contact => "$sip_proto_uri:$register_contact_addr:$contact_port") : ()), 'user-agent' => $sip_user_agent);
		};
		warn localtime . " - Registering to $sip_registrar...\n";
		$sub_register->();
		if ($sip_register_timeout[1]) {
			$ua->loop(\$init_registered);
			die "$0: Cannot register to $sip_registrar\n" if $init_registered <= 0;
		}
	}

	my %send_callbacks = (
		cb_preliminary => sub {
			my ($call, $code, $response) = @_;
			warn localtime . " - Received $code " . $response->msg() . "\n";
		},
		cb_final => sub {
			my ($status, $call, %info) = @_;
			my $error = $call->error();
			my $packet = exists $info{packet} ? $info{packet} : undef;

			if (not defined $error and $status eq 'OK') {
				my $code = defined $packet ? $packet->code() : '';
				my $msg = defined $packet ? $packet->msg() : $status;
				warn localtime . " - Received $code $msg\n";
			} elsif (exists $info{code} and defined $info{code}) {
				my $msg = defined $packet ? $packet->msg() : '';
				warn localtime . " - Received error $info{code} $msg\n";
				$stop = 1;
				return;
			} elsif (exists $info{errno} and defined $info{errno} and $info{errno} =~ /^[1-9][0-9]*$/) {
				$! = int($info{errno});
				warn localtime . " - Error: $!\n";
				$stop = 1;
				return;
			} else {
				warn localtime . " - Error: $error\n";
				$stop = 1;
				return;
			}

			my $param = $call->{param};
			my ($codec, $sdp_addr, $fmt, $ptime);
			my $sdp_peer = $param->{sdp_peer};
			if ($sdp_peer) {
				my @media_peer = $sdp_peer->get_media();
				foreach my $i (0..$#media_peer) {
					my $m = $media_peer[$i];
					$sdp_addr = $m->{addr};
					next unless $m->{proto} eq 'RTP/AVP';
					next unless $m->{media} eq 'audio';
					my $fmts_peer = $m->{fmt};
					next unless $fmts_peer;
					my $ulaw_fmt_peer = $sdp_peer->name2int('PCMU/8000', $i) || 0;
					my $alaw_fmt_peer = $sdp_peer->name2int('PCMA/8000', $i) || 8;
					($ptime) = map { ($_->[0] eq 'a' and $_->[1] =~ /^ptime:\s*([0-9]+)/) ? $1 : () } @{$m->{lines}};
					foreach (@{$fmts_peer}) {
						if ($_ == $ulaw_fmt_peer and grep { $_ eq 'ulaw' } @rtp_codecs) {
							$codec = 'ulaw';
							$fmt = $ulaw_fmt_peer;
							$ptime = 20 unless $ptime;
							last;
						} elsif ($_ == $alaw_fmt_peer and grep { $_ eq 'alaw' } @rtp_codecs) {
							$codec = 'alaw';
							$fmt = $alaw_fmt_peer;
							$ptime = 20 unless $ptime;
							last;
						}
					}
					last if defined $fmt;
				}
			}
			if (not defined $codec) {
				warn localtime . " - No supported codec\n";
				$call->bye();
				return;
			}
			if (ip_addr_is_invalid($sdp_addr) or (ip_addr_is_reserved($sip_peer_host) != ip_addr_is_reserved($sdp_addr) and ip_canonical($sip_peer_host) ne ip_canonical($sdp_addr))) {
				warn localtime . " - Peer is behind NAT and has not announced correct address in SDP, ignoring address from SDP\n";
				my @media_peer = $sdp_peer->get_media();
				my $raddr = $param->{media_raddr};
				foreach my $i (0..$#$raddr) {
					if (not defined $raddr->[$i]) {
						if ($media_peer[$i]->{addr} eq $sdp_addr) {
							my $range = $media_peer[$i]->{range} || 1;
							my @socks = map { ip_parts2sockaddr($sip_peer_host, $media_peer[$i]->{port} + $_) } (0..$range-1);
							$raddr->[$i] = @socks == 1 ? $socks[0] : \@socks;
						}
					} else {
						foreach (ref $raddr->[$i] ? @{$raddr->[$i]} : $raddr->[$i]) {
							my ($addr, $port, $fam) = ip_sockaddr2parts($_);
							$_ = ip_parts2sockaddr($sip_peer_host, $port, $fam) if $addr eq ip_canonical($sdp_addr);
						}
					}
				}
			}
			$param->{rtp_param} = [ $fmt, int(8000*$ptime/1000), $ptime/1000 ];
			$param->{fsms_codec} = $codec;

			warn localtime . " - Call established\n";
		},
	);

	my %receive_callbacks = (
		filter => sub {
			my ($from, $request) = @_;
			return 0 if $stopping;
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
			return 0 if $stopping;
			my $param = $call->{param};
			# This is the only callback which provides peer socket address
			$param->{fsms_peer_addr} = $from->{addr};
			my $refaddr = refaddr($call);
			$calls{$refaddr} = $call;
			weaken($calls{$refaddr});
			return 1;
		},
		cb_invite => sub {
			my ($call, $request) = @_;
			my $param = $call->{param};

			if ($stopping) {
				$call->cleanup();
				return;
			}

			my ($rtp_port, $rtp_sock, $rtcp_sock) = create_rtp_sockets($rtp_listen_addr, 2, $rtp_listen_min_port, $rtp_listen_max_port);
			if (not $rtp_sock or not $rtcp_sock) {
				warn localtime . " - Error: Cannot create rtp or rtcp socket at $rtp_listen_addr from range $rtp_listen_min_port-$rtp_listen_max_port: $!\n";
				$call->cleanup();
				return $request->create_response('503', 'Service Unavailable');
			}

			my ($codec, $sdp_addr_peer, $fmt_peer, $ptime_peer);
			my $sdp_peer = $param->{sdp_peer};
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
				warn localtime . " - Error: No common supported RTP codec\n";
				$call->cleanup();
				return $request->create_response('488', 'Not Acceptable Here');
			}

			if (ip_addr_is_invalid($sdp_addr_peer) or (ip_addr_is_reserved($param->{fsms_peer_addr}) != ip_addr_is_reserved($sdp_addr_peer) and ip_canonical($param->{fsms_peer_addr}) ne ip_canonical($sdp_addr_peer))) {
				warn localtime . " - Peer is behind NAT and has not announced correct address in SDP, ignoring address from SDP\n";
				my @media_peer = $sdp_peer->get_media();
				my $raddr = $param->{media_raddr};
				foreach my $i (0..$#$raddr) {
					if (not defined $raddr->[$i]) {
						if ($media_peer[$i]->{addr} eq $sdp_addr_peer) {
							my $range = $media_peer[$i]->{range} || 1;
							my @socks = map { ip_parts2sockaddr($param->{fsms_peer_addr}, $media_peer[$i]->{port} + $_) } (0..$range-1);
							$raddr->[$i] = @socks == 1 ? $socks[0] : \@socks;
						}
					} else {
						foreach (ref $raddr->[$i] ? @{$raddr->[$i]} : $raddr->[$i]) {
							my ($addr, $port, $fam) = ip_sockaddr2parts($_);
							$_ = ip_parts2sockaddr($param->{fsms_peer_addr}, $port, $fam) if $addr eq ip_canonical($sdp_addr_peer);
						}
					}
				}
				$sdp_addr_peer = $param->{fsms_peer_addr};
			}

			my $codec_name = ($codec eq 'alaw') ? 'PCMA/8000' : 'PCMU/8000';
			my $fmt = $fmt_peer;
			my $ptime = ($rtp_ptime eq 'peer') ? $ptime_peer : $rtp_ptime;
			my $sdp_addr = defined $rtp_public_addr ? $rtp_public_addr : laddr4dst($sdp_addr_peer);
			$sdp_addr =~ s/^\[(.*)\]$/$1/;
			my $contact_addr = defined $sip_public_addr ? $sip_public_addr : laddr4dst($param->{fsms_peer_addr});
			$contact_addr = "[$contact_addr]" if $contact_addr =~ /:/ and $contact_addr !~ /^\[.*\]$/;

			my $init_timer = $call->add_timer(10, sub {
				warn localtime . " - No final ACK was received in 10 seconds\n";
				warn localtime . " - Hangup\n";
				$call->bye();
			});

			my $sdp = eval { Net::SIP::SDP->new(
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
			) };
			if (not defined $sdp) {
				warn localtime . " - Error: SDP parameters are invalid\n";
				$call->cleanup();
				return $request->create_response('488', 'Not Acceptable Here');
			}

			$param->{rtp_param} = [ $fmt, int(8000*$ptime/1000), $ptime/1000 ];
			$param->{sdp} = $sdp;
			$param->{media_lsocks} = [ [ $rtp_sock, $rtcp_sock ] ];
			$param->{fsms_codec} = $codec;
			$param->{fsms_headers} = $request->get_header();
			$param->{fsms_headers}->{request} = [ ($request->as_parts)[1] ];
			$param->{fsms_init_timer} = $init_timer;

			return $request->create_response('200', 'OK', { contact => "$sip_proto_uri:$contact_addr:$contact_port" }, $sdp);
		},
	);

	my %common_callbacks = (
		init_media => sub {
			my ($call, $param) = @_;

			my $init_timer = delete $param->{fsms_init_timer};
			$init_timer->cancel() if $init_timer;

			my $codec = $param->{fsms_codec};
			my $fmt = $param->{rtp_param}->[0];
			my $buffer_size = $param->{rtp_param}->[1];
			my $finish = 0;
			my $established = 0;
			my $stop_send_receive = 0;
			my $state = process_audio_init();

			my $cleanup = sub {
				delete $param->{fsms_cleanup};
				my $state = delete $param->{fsms_state};
				my $timer = delete $param->{fsms_timer};
				process_audio_finish($state) if defined $state;
				store_frag_cache($frag_cache_file) if $mode eq 'receive' and defined $frag_cache_file;
				$timer->cancel() if defined $timer;
				$stop_send_receive = 1;
			};

			my $timer = $call->add_timer(5, sub {
				warn localtime . " - No RTP packet received for 5 seconds\n";
				warn localtime . " - Hangup\n";
				$cleanup->();
				$call->bye();
			});

			my @current_message;
			my @remaining_buffer;

			if ($mode eq 'receive') {
				@current_message = smdll_encode_est();
				@remaining_buffer = ((0) x int(8000*2), @current_message);
				warn localtime . " - Sending connection established\n";
			}

			$param->{fsms_state} = $state;
			$param->{fsms_timer} = $timer;
			$param->{fsms_cleanup} = $cleanup;

			my $tpdu_callback = ($mode eq 'receive') ? sub {
				my ($no_erorr, $type, $payload, @tpdu_data) = @_;
				my $mti = $tpdu_data[1] || 0;
				my $dir = ($role eq 'te') ? 0 : ($role eq 'sc') ? 1 : ($mti == 1) ? 1 : 0;
				my $smsc = parse_call_identity(($dir ? $local_sc_number : $remote_sc_number), $param->{fsms_headers});
				my $smte = parse_call_identity(($dir ? $remote_te_number : $local_te_number), $param->{fsms_headers});
				# TODO: process Status Report with $mti == 2
				process_frag_message($smte, $smsc, $country, $payload, @tpdu_data);
				return;
			} : sub {
				my ($no_erorr, $type, $payload, @tpdu_data) = @_;
				if (not defined $type) {
					return @tpdus ? $tpdus[0] : undef;
				} elsif ($type == $smdll_types{ACK}) {
					# TODO: message successfully sent, store it to disk
					shift @tpdus;
					return @tpdus ? $tpdus[0] : undef;
				} else {
					# TODO: message failed
					shift @tpdus;
					return @tpdus ? $tpdus[0] : undef;
				}
			};

			my $timeout_packets = 0;
			my $send_callback = sub {
				my ($seq, $channel) = @_;
				return if $stop_send_receive;

				$timeout_packets = @remaining_buffer ? 0 : $timeout_packets+1;
				$finish = process_timeout($state, $mode, $role, \@current_message, \@remaining_buffer, $finish, $established, $timeout_packets*$buffer_size/8000);
				if (not @remaining_buffer and $finish) {
					warn localtime . " - Hangup\n";
					$cleanup->();
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
					($finish, my $status) = process_audio_sample($state, $mode, $role, $tpdu_callback, \@current_message, \@remaining_buffer, $finish, $_);
					$established = 1 if defined $status;
				}

				$timer->{expire} = 5 + $call->{dispatcher}->{eventloop}->looptime;
				return;
			};

			my $rtp = $call->rtp('media_send_recv', $send_callback, 1, $receive_callback);
			return invoke_callback($rtp, $call, $param);
		},
		cb_rtp_done => sub {
			# Do nothing, send_callback handle bye
		},
		recv_bye => sub {
			my ($param) = @_;
			warn localtime . " - Other side hangup\n";
			my $init_timer = delete $param->{fsms_init_timer};
			$init_timer->cancel() if $init_timer;
			$param->{fsms_cleanup}->() if exists $param->{fsms_cleanup};
			if ($mode eq 'send') {
				# wait two seconds and reply to additional retransmission of bye packet
				$ua->add_timer(2, sub { warn localtime . " - Call ended\n"; $stop = 1; });
			}
		},
		send_bye => sub {
			my ($param) = @_;
			warn localtime . " - Call ended\n";
		},
		cb_cleanup => sub {
			my ($call) = @_;
			my $param = $call->{param};
			my $init_timer = delete $param->{fsms_init_timer};
			$init_timer->cancel() if $init_timer;
			my $cleanup = delete $param->{fsms_cleanup};
			$cleanup->() if defined $cleanup;
			if ($mode eq 'receive') {
				my $refaddr = refaddr($call);
				delete $calls{$refaddr};
				if ($stopping and not grep { defined $_ } values %calls) {
					warn localtime . " - All calls ended\n";
					$stop_cb->();
				}
			} else {
				$stop_cb->();
			}
		},
	);

	my $call;

	if ($mode eq 'receive') {
		$ua->add_timer(30*60, sub { process_frag_cache($frag_cache_expire, $country) }, 30*60, 'process_frag_cache') if $frag_cache_expire;
		warn localtime . " - Listening at $sip_proto:$sip_listen_addr:$sip_listen_port\n";
		$ua->listen(%receive_callbacks, %common_callbacks);
	} else {
		$rtp_listen_addr = ($sock->sockhost() !~ /^(?:0\.0\.0\.0|::)$/) ? $sock->sockhost() : laddr4dst($sip_peer_host) unless defined $rtp_listen_addr;
		my ($rtp_port, $rtp_sock, $rtcp_sock) = create_rtp_sockets($rtp_listen_addr, 2, $rtp_listen_min_port, $rtp_listen_max_port);
		die "Error: Cannot create rtp socket at $rtp_listen_addr: $!\n" unless defined $rtp_sock;
		die "Error: Cannot create rtcp socket at $rtp_listen_addr: $!\n" unless defined $rtcp_sock;

		my $sdp_addr = defined $rtp_public_addr ? $rtp_public_addr : $rtp_listen_addr;
		my @rtp_map = map { ($_ eq 'ulaw') ? [ 0, 'PCMU/8000' ] : ($_ eq 'alaw') ? [ 8, 'PCMA/8000' ] : () } @rtp_codecs;

		my $sdp = eval { Net::SIP::SDP->new(
			{
				addr => $sdp_addr,
			},
			{
				media => 'audio',
				proto => 'RTP/AVP',
				port => $rtp_port+$rtp_public_port_offset,
				range => 2,
				fmt => [ map { $_->[0] } @rtp_map ],
				a => [
					(map { "rtpmap:$_->[0] $_->[1]" } @rtp_map),
					"ptime:$rtp_ptime",
				],
			},
		) };
		die "Error: Cannot create SDP object: $@\n" unless defined $sdp;

		warn localtime . " - Sending invite to $sip_to via $sip_proto:$sip_peer_host:$sip_peer_port\n";
		$call = $ua->invite($sip_to, media_lsocks => [ [ $rtp_sock, $rtcp_sock ] ], sdp => $sdp, %send_callbacks, %common_callbacks);
	}

	my %defaultsig = ( INT => $SIG{INT}, QUIT => $SIG{QUIT}, TERM => $SIG{TERM} );
	my $sighandler = ($mode eq 'receive') ? sub {
		$SIG{$_} = $defaultsig{$_} foreach keys %defaultsig;
		warn localtime . " - Exit signal, not accepting new calls and scheduling call hangups...\n";
		foreach my $call (grep { defined $_ } values %calls) {
			$call->add_timer(15, sub { $call->bye() if defined $call });
			$stopping = 1;
		}
		if ($stopping) {
			warn localtime . " - Scheduling global stop in 20 seconds\n";
			$ua->add_timer(20, $stop_cb);
		}
		if ($registered) {
			warn localtime . " - Unregistering from $sip_registrar...\n";
			$ua->register(expires => 0, cb_final => $stop_cb, ($register_contact_addr ? (contact => "$sip_proto_uri:$register_contact_addr:$contact_port") : ()), 'user-agent' => $sip_user_agent);
			$ua->add_timer(5, $stop_cb) unless $stopping;
		}
		$stop_cb->() unless $stopping or $registered;
		$stopping = 1;
	} : sub {
		$SIG{$_} = $defaultsig{$_} foreach keys %defaultsig;
		warn localtime . " - Exit signal, not sending remaining messages and scheduling call hangup...\n";
		# TODO
	};
	local ($SIG{INT}, $SIG{QUIT}, $SIG{TERM}) = ($sighandler, $sighandler, $sighandler);
	warn localtime . " - Starting main loop\n";
	$ua->loop(undef, \$stop);
	$ua->cleanup();
	warn localtime . " - Stopped\n";
}


if (grep { $_ eq '--help' } @ARGV) {
	print <<"EOD";
Usage: $0 [ options ]

SIP F-SMS application.

In receive mode - listen for incoming SIP audio
calls, receive V.23 modulated F-SMS messages,
decode them to TPDU and store them either on disk
in RPDU format or send them via email in plain
text + RPDU format.

In send mode - generate TPDU messages, encode
them to F-SMS via V.23 modulation and send via
SIP audio call to remote side.

Both roles are supported, application can act
either as Terminal Equipment or as Service Center.

Options:
  --help                   Show this help
  --protocol=sip           Application protocol: sip (default sip)
  --mode=receive           Application mode: receive (default receive)
  --role=te|sc|dual        Process role: te - Terminal Equipment, sc - Service Center, dual - Dual role based on incoming data (default dual)
  --country=code           Country code for telephone numbers normalization (default none - no normalization)

Receive options:
  --frag-cache=loc,expire  Parts of fragmented messages can be stored either persistant disk file or only in process memory (string "mem") or disabled (string "none"). Incomplete parts expire after specified time (in minutes) and/or at process exit (string "atexit"). Default "mem,1440,atexit"
  --store-to-dir=dir       Specify disk directory where to store received messages in RPDU format (application/vnd.3gpp.sms)
  --send-email=to,from     Specify envelope to recipient and optional from address (default from address is current user)

SIP receive options:
  --local-number=list      List of SIP headers from which is retrieved local receiver telephone number, syntax: header:name|user|tel|/regex/ OR fixed-number OR none (default diversion:tel,diversion:user,to:tel,to:user,request:tel,request:user)
  --remote-number=list     List of SIP headers from which is retrieved remote caller telephone number (default p-asserted-identity:tel,p-asserted-identity:user,p-preferred-identity:tel,p-preferred-identity:user,from:tel,from:user)
  --local-te-number=list   --local-number for te when receiver is in te role (default --local-number)
  --remote-sc-number=list  --remote-number for sc when receiver is in te role (default --remote-number)
  --local-sc-number=list   --local-number for sc when receiver is in sc role (default --local-number)
  --remote-te-number=list  --remote-number for te when receiver is in sc role (default --remtoe-number)
  --sip-identity=identity  SIP identity (default sip-register-user\@sip-register-host or "F-SMS <sip:fsms\@localhost>")
  --sip-accept-uri=regex   Perl regex with SIP URIs for incoming calls (default ^.*\$)
  --sip-register=format    format: proto:user:pass\@host:port (default without registration)
  --sip-register-timeout=f format: expires,init,retry  expires - register expiration (0 - server default), init - initial register attemps, retry - timeout after failed registration (default expires=0 init=1 retry=30)

  --sip-listen=format      format: proto:listen_addr:listen_port/public_addr:public_port (default proto=udp listen_addr=0.0.0.0 listen_port=default_for_proto public_addr=listen_addr public_port=listen_port)
  --rtp-listen=format      format: listen_addr:listen_min_port-listen_max_port/public_addr:public_min_port (default address is sip-listen with default Net::SIP RTP port range)
  --rtp-codecs=codecs      List of allowed codecs separated by comma, chosen codec is by peer preference (default ulaw,alaw)
  --rtp-ptime=ptime        Request receiving and sending RTP packet length in milliseconds (default same length as peer requested from us)

SIP send options:
  --from=number
  --to=number
  --via=number
  --input=format:number:filename
  --message=

  --sip-from   = sip-identity
  --sip-to
  --sip-proxy=proto:user:pass\@host:port

  --sip-listen             Default listen_addr is laddr for peer, listen_port is random
  --rtp-listen
  --rtp-codecs             List is in our prefered order
  --rtp-ptime              Default 20ms

Is is required to specify at least --store-to or --send-email option.
EOD
	exit 1;
}

my %options;
my %multi_options = map { $_ => [] } qw(input);
foreach (@ARGV) {
	die "$0: Invalid argument $_\n" unless $_ =~ /^--([^=]+)=(.*)$/;
	if (exists $multi_options{$1}) {
		push @{$multi_options{$1}}, $2;
	} else {
		die "$0: Option --$1 was already specified\n" if exists $options{$1};
		$options{$1} = $2;
	}
}

my $protocol = exists $options{protocol} ? delete $options{protocol} : 'sip';
die "$0: Unknown protocol $protocol\n" unless $protocol eq 'sip';

my $mode = exists $options{mode} ? delete $options{mode} : 'receive';
die "$0: Unknown mode $mode\n" unless $mode =~ /^(?:send|receive)$/;

my $role = exists $options{role} ? delete $options{role} : ($mode eq 'receive') ? 'dual' : 'te';
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

my ($frag_cache_file, $frag_cache_expire, $frag_cache_disabled, $frag_cache_expire_atexit);

if ($mode eq 'receive') {
	my $frag_cache_opt = exists $options{'frag-cache'} ? delete $options{'frag-cache'} : 'mem';
	die "$0: Invalid --frag-cache option $frag_cache_opt\n" unless $frag_cache_opt =~ /^(.*?|mem|none)(?:,([0-9]+))?(,atexit)?$/ and not ($1 eq 'none' and (defined $2 or defined $3));
	my $frag_cache_file = ($1 ne 'mem' and $1 ne 'none') ? $1 : undef;
	my $frag_cache_expire = (defined $2) ? $2 : 1440;
	my $frag_cache_disabled = ($1 eq 'none');
	my $frag_cache_expire_atexit = (defined $3 or $1 eq 'mem');

	$store_to_dir = delete $options{'store-to-dir'} if exists $options{'store-to-dir'};
	$store_to_dir =~ s/(?<=.)\/$// if defined $store_to_dir;
	die "$0: Directory $store_to_dir does not exist\n" if defined $store_to_dir and not -d $store_to_dir;

	my $send_email = exists $options{'send-email'} ? delete $options{'send-email'} : undef;
	if (defined $send_email) {
		die "$0: Invalid --send-email option $send_email\n" unless $send_email =~ /^([^,]+)(?:,([^,]+))?$/;
		$send_email_env_to = $1;
		$send_email_env_from = $2;
	}
}

my ($from, $to, $via, @tpdus);

if ($mode eq 'send') {
	die "$0: Unsupported role dual in send mode\n" if $role eq 'dual';

	$from = exists $options{from} ? delete $options{from} : undef;
	$to = exists $options{to} ? delete $options{to} : undef;
	$via = exists $options{via} ? delete $options{via} : undef;

	my $message = exists $options{message} ? delete $options{message} : undef;
	if (defined $message) {
		my $number = ($role eq 'sc') ? $from : $to;
		die "$0: Missing number for message\n" unless defined $number;
		my $tpdu;
		if ($role eq 'sc') {
			my @time = localtime(time);
			my $tz = int((timegm(@time) - timelocal(@time)) / 60);
			my $scts = [ 1900+$time[5], 1+$time[4], $time[3], $time[2], $time[1], $time[0], ($tz < 0 ? '-' : ''), int(abs($tz)/60), abs($tz)%60 ];
			$tpdu = tpdu_encode_deliver(0, 0, 0, 0, $number, $scts, 0, 0, 0, undef, 0, 0, $message);
		} else {
			my $sr = 0; # disable status report request
			$tpdu = tpdu_encode_submit(0, $sr, 0, 0, $number, 0, undef, 0, undef, undef, 0, 0, $message);
		}

		push @tpdus, $tpdu;
	}

	foreach (@{$multi_options{input}}) {
		my ($format, $number, $filename) = ($_ =~ /^(?:(rpdu|tpdu|atpdu|inline):)?(?:([^:]*):)?(.*)$/);

		if (not defined $format) {
			if ($filename =~ /\.tpdu$/) {
				$format = 'tpdu';
			} elsif ($filename =~ /\.(?:at)?pdu$/) {
				$format = 'atpdu';
			} elsif ($filename =~ /\.(?:sms|rpdu)$/) {
				$format = 'rpdu';
			} elsif ($filename =~ /\.txt$/) {
				$format = 'txt';
			} else {
				die "$0: Unknown format for input file $filename\n";
			}
		}

		$number = undef if defined $number and not length $number;
		if ($role eq 'sc') {
			die "$0: Originating From and Number for file $filename does not match\n" if defined $from and defined $number and $from ne $number;
			$number = $from unless defined $number;
		} else {
			die "$0: Destination To and Number for file $filename does not match\n" if defined $to and defined $number and $to ne $number;
			$number = $to unless defined $number;
		}

		my ($tpdu, $payload);
		if ($format eq 'inline') {
			$payload = $filename;
		} else {
			my $fh;
			if ($filename eq '-') {
				$fh = *STDIN;
				binmode $fh, ':raw';
			} else {
				open $fh, '<:raw', $filename or die "$0: Cannot open input file $filename: $!\n";
			}
			$payload = do { local $/; <$fh> };
			close $fh;
			die "$0: Cannot read input file $filename\n" unless defined $payload;
		}

		if ($format eq 'tpdu') {
			$tpdu = $payload;
		} elsif ($format eq 'atpdu') {
			(undef, $tpdu) = atpdu_decode($payload);
		} elsif ($format eq 'rpdu') {
			(undef, undef, undef, $tpdu) = rpdu_decode($payload);
		} elsif ($format eq 'txt' or $format eq 'inline') {
			die "$0: Missing number for input text file $filename\n" unless defined $number;
			if ($role eq 'sc') {
				my @time = localtime(time);
				my $tz = int((timegm(@time) - timelocal(@time)) / 60);
				my $scts = [ 1900+$time[5], 1+$time[4], $time[3], $time[2], $time[1], $time[0], ($tz < 0 ? '-' : ''), int(abs($tz)/60), abs($tz)%60 ];
				$tpdu = tpdu_encode_deliver(0, 0, 0, 0, $number, $scts, 0, 0, 0, undef, 0, 0, $payload);
			} else {
				my $sr = 0; # disable status report request
				$tpdu = tpdu_encode_submit(0, $sr, 0, 0, $number, 0, undef, 0, undef, undef, 0, 0, $payload);
			}
		} else {
			die "$0: Unsupported input format $format\n";
		}
		die "$0: Broken input file $filename\n" unless defined $tpdu;

		my ($mti, @tpdu_data) = tpdu_decode($tpdu);
		die "$0: Broken input file $filename\n" unless defined $mti;
		if ($role eq 'sc' and $mti == 1) {
			die "$0: Missing number for file $filename\n" unless defined $number;
			$tpdu_data[6] = $number;
			my @time = localtime(time);
			my $tz = int((timegm(@time) - timelocal(@time)) / 60);
			my $scts = [ 1900+$time[5], 1+$time[4], $time[3], $time[2], $time[1], $time[0], ($tz < 0 ? '-' : ''), int(abs($tz)/60), abs($tz)%60 ];
			$tpdu_data[7] = $scts;
			$tpdu = tpdu_encode(0, @tpdu_data);
		} elsif ($role eq 'te' and $mti != 1) {
			die "$0: Input file $filename is status report\n" if $mti == 2;
			die "$0: Missing number for file $filename\n" unless defined $number;
			$tpdu_data[6] = $number;
			$tpdu = tpdu_encode(1, @tpdu_data);
		}

		push @tpdus, $tpdu;
	}
}

my ($sip_auth_user, $sip_auth_pass);

my $sip_to = exists $options{'sip-to'} ? delete $options{'sip-to'} : undef;
my $sip_proxy = exists $options{'sip-proxy'} ? delete $options{'sip-proxy'} : '';
die "$0: Invalid --sip-proxy option $sip_proxy\n" unless $sip_proxy =~ /^(?:(tcp|udp|tls):)?(?:([^:]+)(?::([^@]+))?\@)?([^\[\]<>\/:]*|\[[^\[\]<>\/]*\])(?::([0-9]+))?$/;
my $sip_peer_proto = $1;
$sip_auth_user = $2 if defined $2;
$sip_auth_pass = $3 if defined $3;
my $sip_peer_host = (length $4) ? $4 : undef;
my $sip_peer_port = (defined $5) ? $5 : (not defined $sip_peer_host) ? undef : (defined $sip_peer_proto and $sip_peer_proto eq 'tls') ? 5061 : 5060;
if (not defined $sip_peer_host and defined $sip_to) {
	my ($sip_to_uri) = sip_split_name_addr($sip_to);
	my ($sip_to_domain, $sip_to_user, $sip_to_proto) = sip_uri2parts($sip_to_uri);
	$sip_to_domain =~ /^(.*?)(?::(\w+))?$/;
	my ($sip_to_host, $sip_to_port) = ($1, $2);
	$sip_peer_host = $sip_to_host;
	$sip_peer_port = defined $sip_to_port ? $sip_to_port : $sip_to_proto eq 'sips' ? 5061 : 5060;
}

my $sip_register = exists $options{'sip-register'} ? delete $options{'sip-register'} : '';
die "$0: Invalid --sip-register $sip_register\n" unless $sip_register =~ /^(?:(tcp|udp|tls):)?(?:([^:]+)(?::([^@]+))?\@)?([^:]*|\[[^\]]*\])(?::([0-9]+))?$/;
my $sip_register_proto = $1;
$sip_auth_user = $2 if defined $2;
$sip_auth_pass = $3 if defined $3;
my $sip_register_host = (length $4) ? $4 : undef;
my $sip_register_port = (defined $5) ? $5 : undef;
my $sip_register_timeout = exists $options{'sip-register-timeout'} ? delete $options{'sip-register-timeout'} : '';
die "$0: Invalid --sip-register-timeout $sip_register_timeout\n" unless $sip_register_timeout =~ /^(?:([1-9][0-9]*)(?:,([0-9]+)(?:,([1-9][0-9]*))))?$/;
my @sip_register_timeout = split /,/, $sip_register_timeout;
$sip_register_timeout[0] = 3600 unless defined $sip_register_timeout[0];
$sip_register_timeout[1] = 1 unless defined $sip_register_timeout[1];
$sip_register_timeout[2] = 30 unless defined $sip_register_timeout[2];

my $sip_listen = exists $options{'sip-listen'} ? delete $options{'sip-listen'} : '';
die "$0: Invalid --sip-listen option $sip_listen\n" unless $sip_listen =~ /^(?:(tcp|udp|tls):)?([^\[\]<>\/:]*|\[[^\[\]<>\/]*\])(?::([0-9]+))?(?:\/([^\[\]<>\/:]*|\[[^\[\]<>\/]*\])(?::([0-9]+))?)?$/;
my $sip_proto = (defined $1) ? $1 : (defined $sip_peer_proto) ? $sip_peer_proto : (defined $sip_register_proto) ? $sip_register_proto : 'udp';
die "$0: Protocol for --sip-listen and --sip-proxy does not match\n" if defined $sip_proto and defined $sip_peer_proto and $sip_proto ne $sip_peer_proto;
die "$0: Protocol for --sip-listen and --sip-register does not match\n" if defined $sip_proto and defined $sip_register_proto and $sip_proto ne $sip_register_proto;
my $sip_listen_addr = (length $2) ? $2 : undef;
my $sip_listen_port = (defined $3) ? $3 : ($mode eq 'send' or defined $sip_register_host) ? undef : ($sip_proto eq 'tls') ? 5061 : 5060;
my $sip_public_addr = (defined $4 and length $4) ? $4 : undef;
my $sip_public_port = (defined $5) ? $5 : $sip_listen_port;

my $sip_from = exists $options{'sip-from'} ? delete $options{'sip-from'} : ((($sip_proto eq 'tls') ? 'sips' : 'sip') . ':' . ((defined $sip_auth_user) ? $sip_auth_user : (defined $from and $role eq 'te') ? $from : (defined $via and $role eq 'sc') ? $via : 'fsms') . '@' . ((defined $sip_peer_host) ? $sip_peer_host : 'localhost'));

$sip_listen_addr = ((defined $sip_peer_host and $sip_peer_host =~ /:/) or (defined $sip_register_host and $sip_register_host =~ /:/)) ? '[::]' : '0.0.0.0' if not defined $sip_listen_addr and $mode ne 'send';
die "$0: IP protocol for --sip-listen and --sip-proxy does not match\n" if defined $sip_peer_host and defined $sip_listen_addr and (($sip_peer_host =~ /:/ and $sip_listen_addr !~ /:/) or ($sip_peer_host =~ /^[0-9]+\.[0-9]+\.[0-9]+\.[0-9]+$/ and $sip_listen_addr =~ /:/));
die "$0: IP protocol for --sip-listen and --sip-register does not match\n" if defined $sip_register_host and (($sip_register_host =~ /:/ and $sip_listen_addr !~ /:/) or ($sip_register_host =~ /^[0-9]+\.[0-9]+\.[0-9]+\.[0-9]+$/ and $sip_listen_addr =~ /:/));
$sip_public_addr = $sip_listen_addr unless defined $sip_public_addr;
$sip_public_addr = undef if defined $sip_public_addr and ip_addr_is_wildcard($sip_public_addr);

sub parse_number_option {
	my ($option, $default) = @_;
	my $number = exists $options{$option} ? delete $options{$option} : $default;
	return $number if ref $number;
	$number = $number . $default if $number =~ /,$/;
	$number = $default . $number if $number =~ /^,/;
	my @number;
	if (defined $number) {
		my @parts = split /(?<!\\),/, $number;
		$_ =~ s/\\,/,/g foreach @parts;
		@parts = () if @parts == 1 and $parts[0] eq 'none';
		die "$0: Invalid format for --$option\n" if @parts > 1 and grep { $_ !~ /^[^:]+:(?:name|user|tel|\/.*\/)$/ } @parts;
		foreach (@parts) {
			if ($_ =~ /^([^:]+):(.*)$/) {
				push @number, [ lc $1, ($2 =~ /^\/(.*)\/$/) ? qr/$1/ : $2 ];
			} else {
				die "$0: Invalid fixed number in --$option\n" unless $_ =~ /^\+?[0-9*#a-cA-C]+$/;
				push @number, $_;
			}
		}
	}
	return \@number;
}
my $local_number = parse_number_option('local-number', 'diversion:tel,diversion:user,to:tel,to:user,request:tel,request:user');
my $local_sc_number = parse_number_option('local-sc-number', $local_number);
my $local_te_number = parse_number_option('local-te-number', $local_number);
my $remote_number = parse_number_option('remote-number', 'p-asserted-identity:tel,p-asserted-identity:user,p-preferred-identity:tel,p-preferred-identity:user,from:tel,from:user');
my $remote_sc_number = parse_number_option('remote-sc-number', $remote_number);
my $remote_te_number = parse_number_option('remote-te-number', $remote_number);

my $sip_identity = exists $options{'sip-identity'} ? delete $options{'sip-identity'} : ('F-SMS <' . (($sip_proto eq 'tls') ? 'sips' : 'sip') . ':' . ((defined $sip_auth_user) ? $sip_auth_user : 'fsms') . '@' . ((defined $sip_register_host) ? $sip_register_host : 'localhost') . '>');
my $sip_accept_uri_re = exists $options{'sip-accept-uri'} ? delete $options{'sip-accept-uri'} : undef;
$sip_accept_uri_re = qr/$sip_accept_uri_re/ if defined $sip_accept_uri_re;

my $rtp_listen = exists $options{'rtp-listen'} ? delete $options{'rtp-listen'} : defined $sip_listen_addr ? $sip_listen_addr : '';
die "$0: Invalid --rtp-listen option $rtp_listen\n" unless $rtp_listen =~ /^([^\[\]<>\/:]*|\[[^\[\]<>\/]*\])(?::([0-9]+)-([0-9]+))?(?:\/([^\[\]<>\/:]*|\[[^\[\]<>\/]*\])(?::([0-9]+))?)?$/;
my $rtp_listen_addr = (length $1) ? $1 : $sip_listen_addr;
my $rtp_listen_min_port = (defined $2) ? $2 : $Net::SIP::Util::RTP_MIN_PORT;
my $rtp_listen_max_port = (defined $3) ? $3 : $Net::SIP::Util::RTP_MAX_PORT;
die "$0: Invalid RTP listen max port $rtp_listen_max_port\n" if $rtp_listen_max_port < $rtp_listen_min_port+1 or $rtp_listen_max_port >= 2**16;
my $rtp_public_addr = (defined $4 and length $4) ? $4 : $rtp_listen_addr;
$rtp_public_addr = undef if defined $rtp_public_addr and ip_addr_is_wildcard($rtp_public_addr);
my $rtp_public_port_offset = (defined $5) ? ($5-$rtp_listen_min_port) : 0;
die "$0: Invalid RTP public min port $5\n" if $rtp_listen_max_port+$rtp_public_port_offset >= 2**16;

my @rtp_codecs = exists $options{'rtp-codecs'} ? (split /,/, delete $options{'rtp-codecs'}) : qw(ulaw alaw);
die "$0: Invalid RTP codec $_\n" foreach grep { $_ !~ /^(?:ulaw|alaw)$/ } @rtp_codecs;
my $rtp_ptime = exists $options{'rtp-ptime'} ? $options{'rtp-ptime'} : 'peer';
die "$0: Invalid RTP ptime $rtp_ptime\n" unless $rtp_ptime =~ /^(?:[0-9]+|peer)$/;

my ($extra_key) = sort keys %options;
die "$0: Unknown option --$extra_key\n" if defined $extra_key;

if ($mode eq 'receive') {
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
}

protocol_sip_loop(
	mode => $mode,
	role => $role,
	country => $country,
	frag_cache_file => $frag_cache_file,
	frag_cache_expire => $frag_cache_expire,
	local_sc_number => $local_sc_number,
	local_te_number => $local_te_number,
	remote_sc_number => $remote_sc_number,
	remote_te_number => $remote_te_number,
	sip_identity => $sip_identity,
	sip_accept_uri_re => $sip_accept_uri_re,
	sip_proto => $sip_proto,
	sip_auth_user => $sip_auth_user,
	sip_auth_pass => $sip_auth_pass,
	sip_register_host => $sip_register_host,
	sip_register_port => $sip_register_port,
	sip_register_timeout => \@sip_register_timeout,
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
) if $mode eq 'receive';

protocol_sip_loop(
	mode => $mode,
	role => $role,
	country => $country,
	tpdus => \@tpdus,
	sip_from => $sip_from,
	sip_to => $sip_to,
	sip_auth_user => $sip_auth_user,
	sip_auth_pass => $sip_auth_pass,
	sip_peer_host => $sip_peer_host,
	sip_peer_port => $sip_peer_port,
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
) if $mode eq 'send';

process_frag_cache(-1, $country) if $frag_cache_expire_atexit;
store_frag_cache($frag_cache_file) if defined $frag_cache_file;
