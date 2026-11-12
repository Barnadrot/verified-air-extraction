import DivRemFV.ProductWitness32
import DivRemFV.Generated.IntegerRows

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def unsigned32NonzeroWitness (a b q r w col : Nat) : Nat :=
  match col with
  | 0 => a / 65536
  | 1 => a % 65536
  | 2 => b / 65536
  | 3 => b % 65536
  | 4 => q / 65536
  | 5 => q % 65536
  | 6 => r / 65536
  | 7 => r % 65536
  | 8 => w / 65536
  | 9 => w % 65536
  | 10 => q * b / 65536
  | 11 => q * b % 65536
  | 12 => a / 65536
  | 13 => a % 65536
  | 14 => b / 65536
  | 15 => b % 65536
  | 16 => 0
  | 17 => 1
  | 18 => q % 32768
  | 19 => q / 32768 % 2
  | 20 => q / 65536 % 16384
  | 21 => q / 1073741824
  | 22 => digit15 q 1
  | 23 => b % 32768
  | 24 => b / 32768 % 2
  | 25 => b / 65536 % 16384
  | 26 => b / 1073741824
  | 27 => digit15 b 1
  | 28 => partial32 q b 0 0 % 32768
  | 29 => partial32 q b 0 0 / 32768
  | 30 => partial32 q b 0 1 % 32768
  | 31 => partial32 q b 0 1 / 32768
  | 32 => partial32 q b 0 2 % 32768
  | 33 => partial32 q b 0 2 / 32768
  | 34 => partial32 q b 1 0 % 32768
  | 35 => partial32 q b 1 0 / 32768
  | 36 => partial32 q b 1 1 % 32768
  | 37 => partial32 q b 1 1 / 32768
  | 38 => partial32 q b 1 2 % 32768
  | 39 => partial32 q b 1 2 / 32768
  | 40 => partial32 q b 2 0 % 32768
  | 41 => partial32 q b 2 0 / 32768
  | 42 => partial32 q b 2 1 % 32768
  | 43 => partial32 q b 2 1 / 32768
  | 44 => partial32 q b 2 2
  | 45 => middle32 q b % 32768 % 2
  | 46 => middle32 q b % 32768 / 2
  | 47 => middle32 q b / 32768
  | 48 => next32 q b + middle32 q b / 32768
  | 49 => ((q * b) % 65536 + r % 65536) / 65536
  | 50 => (r % 65536 + w % 65536 + 1) / 65536
  | 51 => 1
  | 52 => ((((b / 65536 : Nat) : K) + ((b % 65536 : Nat) : K))⁻¹).val
  | _ => 0

theorem unsigned32_nonzero_witness_bounds (a b q r w : Nat)
    (aBound : a < 4294967296) (bBound : b < 4294967296)
    (qBound : q < 4294967296) (rBound : r < 4294967296) (wBound : w < 4294967296)
    (identity : a = q * b + r) :
    Bounds63 (unsigned32NonzeroWitness a b q r w) := by
  have productBound : q * b < 4294967296 := by omega
  have merged := product32_merge q b productBound
  have middleBound := product32_middle_bound q b qBound bBound
  have p00 := partial32_bound q b 0 0 qBound bBound
  have p01 := partial32_bound q b 0 1 qBound bBound
  have p02 := partial32_bound q b 0 2 qBound bBound
  have p10 := partial32_bound q b 1 0 qBound bBound
  have p11 := partial32_bound q b 1 1 qBound bBound
  have p12 := partial32_bound q b 1 2 qBound bBound
  have p20 := partial32_bound q b 2 0 qBound bBound
  have p21 := partial32_bound q b 2 1 qBound bBound
  have lastBound : partial32 q b 2 2 < 16 := by
    change q / 1073741824 * (b / 1073741824) < 16
    have qCap : q / 1073741824 ≤ 3 := by omega
    have bCap : b / 1073741824 ≤ 3 := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul qCap bCap) (by decide)
  have p02Small : partial32 q b 0 2 < 131072 := by
    have qCap : q % 32768 ≤ 32767 := by omega
    have bCap : b / 1073741824 ≤ 3 := by omega
    have bound := Nat.mul_le_mul qCap bCap
    norm_num [partial32, digit15]
    omega
  have p12Small : partial32 q b 1 2 < 131072 := by
    have qCap : q / 32768 % 32768 ≤ 32767 := by omega
    have bCap : b / 1073741824 ≤ 3 := by omega
    have bound := Nat.mul_le_mul qCap bCap
    norm_num [partial32, digit15]
    omega
  have p20Small : partial32 q b 2 0 < 131072 := by
    have qCap : q / 1073741824 ≤ 3 := by omega
    have bCap : b % 32768 ≤ 32767 := by omega
    have bound := Nat.mul_le_mul qCap bCap
    norm_num [partial32, digit15]
    omega
  have p21Small : partial32 q b 2 1 < 131072 := by
    have qCap : q / 1073741824 ≤ 3 := by omega
    have bCap : b / 32768 % 32768 ≤ 32767 := by omega
    have bound := Nat.mul_le_mul qCap bCap
    norm_num [partial32, digit15]
    omega
  constructor <;> norm_num only [unsigned32NonzeroWitness, digit15] <;> omega

def unsigned32ZeroWitness (a col : Nat) : Nat :=
  match col with
  | 0 | 6 => a / 65536
  | 1 | 7 => a % 65536
  | 4 | 5 => 65535
  | 51 => 1
  | _ => 0

theorem unsigned32_zero_witness_bounds (a : Nat) (aBound : a < 4294967296) :
    Bounds63 (unsigned32ZeroWitness a) := by
  constructor <;> norm_num only [unsigned32ZeroWitness] <;> omega

theorem unsigned32_zero_witness_field (a : Nat) :
    Equations63 (fun col => (unsigned32ZeroWitness a col : K)) := by
  constructor <;> norm_num [unsigned32ZeroWitness]

end DivRemFV

