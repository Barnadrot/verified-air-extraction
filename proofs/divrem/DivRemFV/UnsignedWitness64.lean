import DivRemFV.ProductWitness64
import DivRemFV.Generated.IntegerRows

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def unsigned64NonzeroWitness (a b q r w col : Nat) : Nat :=
  match col with
  | 0 => a / 281474976710656
  | 1 => a / 4294967296 % 65536
  | 2 => a / 65536 % 65536
  | 3 => a % 65536
  | 4 => b / 281474976710656
  | 5 => b / 4294967296 % 65536
  | 6 => b / 65536 % 65536
  | 7 => b % 65536
  | 8 => q / 281474976710656
  | 9 => q / 4294967296 % 65536
  | 10 => q / 65536 % 65536
  | 11 => q % 65536
  | 12 => r / 281474976710656
  | 13 => r / 4294967296 % 65536
  | 14 => r / 65536 % 65536
  | 15 => r % 65536
  | 16 => w / 281474976710656
  | 17 => w / 4294967296 % 65536
  | 18 => w / 65536 % 65536
  | 19 => w % 65536
  | 20 => (q * b) / 281474976710656
  | 21 => (q * b) / 4294967296 % 65536
  | 22 => (q * b) / 65536 % 65536
  | 23 => (q * b) % 65536
  | 24 => a / 281474976710656
  | 25 => a / 4294967296 % 65536
  | 26 => a / 65536 % 65536
  | 27 => a % 65536
  | 28 => b / 281474976710656
  | 29 => b / 4294967296 % 65536
  | 30 => b / 65536 % 65536
  | 31 => b % 65536
  | 32 => 0
  | 33 => 1
  | 34 => q % 32768
  | 35 => q / 32768 % 2
  | 36 => q / 65536 % 16384
  | 37 => q / 1073741824 % 4
  | 38 => q / 4294967296 % 8192
  | 39 => q / 35184372088832 % 8
  | 40 => q / 281474976710656 % 4096
  | 41 => q / 1152921504606846976
  | 42 => digit15 q 1
  | 43 => digit15 q 2
  | 44 => digit15 q 3
  | 45 => b % 32768
  | 46 => b / 32768 % 2
  | 47 => b / 65536 % 16384
  | 48 => b / 1073741824 % 4
  | 49 => b / 4294967296 % 8192
  | 50 => b / 35184372088832 % 8
  | 51 => b / 281474976710656 % 4096
  | 52 => b / 1152921504606846976
  | 53 => digit15 b 1
  | 54 => digit15 b 2
  | 55 => digit15 b 3
  | 56 => partial64 q b 0 0 % 32768
  | 57 => partial64 q b 0 0 / 32768
  | 58 => partial64 q b 0 1 % 32768
  | 59 => partial64 q b 0 1 / 32768
  | 60 => partial64 q b 0 2 % 32768
  | 61 => partial64 q b 0 2 / 32768
  | 62 => partial64 q b 0 3 % 32768
  | 63 => partial64 q b 0 3 / 32768
  | 64 => partial64 q b 0 4 % 32768
  | 65 => partial64 q b 0 4 / 32768
  | 66 => partial64 q b 1 0 % 32768
  | 67 => partial64 q b 1 0 / 32768
  | 68 => partial64 q b 1 1 % 32768
  | 69 => partial64 q b 1 1 / 32768
  | 70 => partial64 q b 1 2 % 32768
  | 71 => partial64 q b 1 2 / 32768
  | 72 => partial64 q b 1 3 % 32768
  | 73 => partial64 q b 1 3 / 32768
  | 74 => partial64 q b 1 4 % 32768
  | 75 => partial64 q b 1 4 / 32768
  | 76 => partial64 q b 2 0 % 32768
  | 77 => partial64 q b 2 0 / 32768
  | 78 => partial64 q b 2 1 % 32768
  | 79 => partial64 q b 2 1 / 32768
  | 80 => partial64 q b 2 2 % 32768
  | 81 => partial64 q b 2 2 / 32768
  | 82 => partial64 q b 2 3 % 32768
  | 83 => partial64 q b 2 3 / 32768
  | 84 => partial64 q b 2 4 % 32768
  | 85 => partial64 q b 2 4 / 32768
  | 86 => partial64 q b 3 0 % 32768
  | 87 => partial64 q b 3 0 / 32768
  | 88 => partial64 q b 3 1 % 32768
  | 89 => partial64 q b 3 1 / 32768
  | 90 => partial64 q b 3 2 % 32768
  | 91 => partial64 q b 3 2 / 32768
  | 92 => partial64 q b 3 3 % 32768
  | 93 => partial64 q b 3 3 / 32768
  | 94 => partial64 q b 3 4 % 32768
  | 95 => partial64 q b 3 4 / 32768
  | 96 => partial64 q b 4 0 % 32768
  | 97 => partial64 q b 4 0 / 32768
  | 98 => partial64 q b 4 1 % 32768
  | 99 => partial64 q b 4 1 / 32768
  | 100 => partial64 q b 4 2 % 32768
  | 101 => partial64 q b 4 2 / 32768
  | 102 => partial64 q b 4 3 % 32768
  | 103 => partial64 q b 4 3 / 32768
  | 104 => partial64 q b 4 4
  | 105 => merged64 q b 1 % 32768 % 2
  | 106 => merged64 q b 1 % 32768 / 2
  | 107 => merged64 q b 1 / 32768
  | 108 => merged64 q b 2 % 32768 % 4
  | 109 => merged64 q b 2 % 32768 / 4
  | 110 => merged64 q b 2 / 32768
  | 111 => merged64 q b 3 % 32768 % 8
  | 112 => merged64 q b 3 % 32768 / 8
  | 113 => merged64 q b 3 / 32768
  | 114 => merged64 q b 4
  | 115 => ((q * b) % 65536 + r % 65536) / 65536
  | 116 => ((q * b) % 4294967296 + r % 4294967296) / 4294967296
  | 117 => ((q * b) % 281474976710656 + r % 281474976710656) / 281474976710656
  | 118 => (r % 65536 + w % 65536 + 1) / 65536
  | 119 => (r % 4294967296 + w % 4294967296 + 1) / 4294967296
  | 120 => (r % 281474976710656 + w % 281474976710656 + 1) / 281474976710656
  | 121 => 1
  | 122 => (((b / 281474976710656 : Nat) : K) + ((b / 4294967296 % 65536 : Nat) : K) + ((b / 65536 % 65536 : Nat) : K) + ((b % 65536 : Nat) : K))⁻¹ |>.val
  | _ => 0

theorem unsigned64_nonzero_witness_bounds (a b q r w : Nat)
    (aBound : a < 18446744073709551616) (bBound : b < 18446744073709551616)
    (qBound : q < 18446744073709551616) (rBound : r < 18446744073709551616)
    (wBound : w < 18446744073709551616) (identity : a = q * b + r) :
    Bounds61 (unsigned64NonzeroWitness a b q r w) := by
  have productBound : q * b < 18446744073709551616 := by omega
  have merged := product64_merge q b productBound
  have carry := product64_carry_bounds q b qBound bBound
  have p00 := partial64_bound q b 0 0 qBound bBound
  have p01 := partial64_bound q b 0 1 qBound bBound
  have p02 := partial64_bound q b 0 2 qBound bBound
  have p03 := partial64_bound q b 0 3 qBound bBound
  have p04 := partial64_bound q b 0 4 qBound bBound
  have e04 := partial64_edge_bound q b 0 4 qBound bBound (by decide)
  have p10 := partial64_bound q b 1 0 qBound bBound
  have p11 := partial64_bound q b 1 1 qBound bBound
  have p12 := partial64_bound q b 1 2 qBound bBound
  have p13 := partial64_bound q b 1 3 qBound bBound
  have p14 := partial64_bound q b 1 4 qBound bBound
  have e14 := partial64_edge_bound q b 1 4 qBound bBound (by decide)
  have p20 := partial64_bound q b 2 0 qBound bBound
  have p21 := partial64_bound q b 2 1 qBound bBound
  have p22 := partial64_bound q b 2 2 qBound bBound
  have p23 := partial64_bound q b 2 3 qBound bBound
  have p24 := partial64_bound q b 2 4 qBound bBound
  have e24 := partial64_edge_bound q b 2 4 qBound bBound (by decide)
  have p30 := partial64_bound q b 3 0 qBound bBound
  have p31 := partial64_bound q b 3 1 qBound bBound
  have p32 := partial64_bound q b 3 2 qBound bBound
  have p33 := partial64_bound q b 3 3 qBound bBound
  have p34 := partial64_bound q b 3 4 qBound bBound
  have e34 := partial64_edge_bound q b 3 4 qBound bBound (by decide)
  have p40 := partial64_bound q b 4 0 qBound bBound
  have e40 := partial64_edge_bound q b 4 0 qBound bBound (by decide)
  have p41 := partial64_bound q b 4 1 qBound bBound
  have e41 := partial64_edge_bound q b 4 1 qBound bBound (by decide)
  have p42 := partial64_bound q b 4 2 qBound bBound
  have e42 := partial64_edge_bound q b 4 2 qBound bBound (by decide)
  have p43 := partial64_bound q b 4 3 qBound bBound
  have e43 := partial64_edge_bound q b 4 3 qBound bBound (by decide)
  have last := partial64_last_bound q b qBound bBound
  constructor
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - aBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - aBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - aBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - aBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - rBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - rBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - rBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - rBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - wBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - wBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - wBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - wBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - productBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - productBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - productBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - productBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - aBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - aBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - aBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - aBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - qBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - bBound; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p00; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p00; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p01; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p01; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p02; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p02; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p03; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p03; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e04; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e04; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p10; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p10; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p11; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p11; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p12; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p12; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p13; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p13; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e14; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e14; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p20; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p20; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p21; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p21; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p22; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p22; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p23; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p23; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e24; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e24; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p30; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p30; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p31; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p31; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p32; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p32; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p33; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - p33; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e34; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e34; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e40; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e40; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e41; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e41; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e42; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e42; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e43; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - e43; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - last; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - carry; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - carry; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - carry; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - merged; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)
  · norm_num only [unsigned64NonzeroWitness, digit15] <;>
      (clear * - a b q r w; omega)

def unsigned64ZeroWitness (a col : Nat) : Nat :=
  match col with
  | 0 | 12 => a / 281474976710656
  | 1 | 13 => a / 4294967296 % 65536
  | 2 | 14 => a / 65536 % 65536
  | 3 | 15 => a % 65536
  | 8 | 9 | 10 | 11 => 65535
  | 121 => 1
  | _ => 0

theorem unsigned64_zero_witness_bounds (a : Nat) (aBound : a < 18446744073709551616) :
    Bounds61 (unsigned64ZeroWitness a) := by
  constructor <;> norm_num only [unsigned64ZeroWitness] <;> omega

theorem unsigned64_zero_witness_field (a : Nat) :
    Equations61 (fun col => (unsigned64ZeroWitness a col : K)) := by
  constructor <;> norm_num [unsigned64ZeroWitness]

end DivRemFV

