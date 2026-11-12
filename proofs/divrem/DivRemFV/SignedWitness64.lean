import DivRemFV.DivisionNatRows

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DivRemFV
open Generated

def signed64Witness (a b q r col : Nat) : Nat :=
  let sa := signValue 64 a
  let sb := signValue 64 b
  let qo := if b=0 then 18446744073709551615 else if sa=sb then q else negateNat 64 q
  let ro := if b=0 then a else if sa=0 then r else negateNat 64 r
  match col with
  | 0 => a/281474976710656
  | 1 => a/4294967296%65536
  | 2 => a/65536%65536
  | 3 => a%65536
  | 4 => b/281474976710656
  | 5 => b/4294967296%65536
  | 6 => b/65536%65536
  | 7 => b%65536
  | 8 => qo/281474976710656
  | 9 => qo/4294967296%65536
  | 10 => qo/65536%65536
  | 11 => qo%65536
  | 12 => ro/281474976710656
  | 13 => ro/4294967296%65536
  | 14 => ro/65536%65536
  | 15 => ro%65536
  | 16 => q/281474976710656
  | 17 => q/4294967296%65536
  | 18 => q/65536%65536
  | 19 => q%65536
  | 20 => r/281474976710656
  | 21 => r/4294967296%65536
  | 22 => r/65536%65536
  | 23 => r%65536
  | 24 => sa
  | 25 => magnitudeNat 64 a/281474976710656
  | 26 => magnitudeNat 64 a/4294967296%65536
  | 27 => magnitudeNat 64 a/65536%65536
  | 28 => magnitudeNat 64 a%65536
  | 29 => magnitudeNat 64 b/281474976710656
  | 30 => magnitudeNat 64 b/4294967296%65536
  | 31 => magnitudeNat 64 b/65536%65536
  | 32 => magnitudeNat 64 b%65536
  | 33 => sb
  | 34 => a/281474976710656%32768
  | 35 => a/4294967296%65536
  | 36 => a/65536%65536
  | 37 => a%65536
  | 38 => b/281474976710656%32768
  | 39 => b/4294967296%65536
  | 40 => b/65536%65536
  | 41 => b%65536
  | 42 => if b=0 then 0 else 1
  | 43 => 1
  | 44 => if b≠0 ∧ sa≠sb then 1 else 0
  | 45 => if b≠0 ∧ sa=1 then 1 else 0
  | 46 => (((b/281474976710656 : Nat) : K)+((b/4294967296%65536 : Nat) : K)+
      ((b/65536%65536 : Nat) : K)+((b%65536 : Nat) : K))⁻¹ |>.val
  | _ => 0

theorem signed64_witness_bounds (a b q r : Nat)
    (ab : a < 18446744073709551616) (bb : b < 18446744073709551616)
    (qb : q < 18446744073709551616) (rb : r < 18446744073709551616) : Bounds62 (signed64Witness a b q r) := by
  constructor <;> simp only [signed64Witness,signValue,magnitudeNat,negateNat] <;>
    norm_num only <;> (try split_ifs) <;> omega

theorem signed64_witness_integer (a b q r : Nat)
    (ab : a < 18446744073709551616) (bb : b < 18446744073709551616) :
    IntegerEquations62 (fun col => (signed64Witness a b q r col : Int)) := by
  by_cases sa : a < 9223372036854775808 <;> by_cases sb : b < 9223372036854775808 <;> by_cases bz : b=0 <;>
    constructor <;> norm_num [signed64Witness,signValue,sa,sb,bz] <;> omega

theorem signed64_divisor_sum_nonzero (b : Nat) (cap : b < 18446744073709551616) (nonzero : b≠0) :
    ((b/281474976710656 : Nat) : K)+((b/4294967296%65536 : Nat) : K)+
      ((b/65536%65536 : Nat) : K)+((b%65536 : Nat) : K) ≠ 0 := by
  intro eq
  have cast : ((b/281474976710656+b/4294967296%65536+b/65536%65536+b%65536 : Nat) : K) = 0 := by
    simpa only [Nat.cast_add] using eq
  have value := lift_field_equality _ 0 (by dsimp [fieldModulus]; omega) (by decide) cast
  have packing := split16_64 b
  omega

theorem signed64_witness_field (a b q r : Nat)
    (ab : a < 18446744073709551616) (bb : b < 18446744073709551616) :
    Equations62 (fun col => (signed64Witness a b q r col : K)) := by
  apply integer_to_field62 _ (signed64_witness_integer a b q r ab bb)
  · by_cases bz : b=0
    · subst b; norm_num [signed64Witness]
    · have inverse := mul_inv_cancel₀ (signed64_divisor_sum_nonzero b bb bz)
      simpa only [signed64Witness,zero_add,one_mul,mul_one,ZMod.natCast_zmod_val,
        inverse,sub_self,mul_zero]
  · by_cases bz : b=0
    · subst b; norm_num [signed64Witness]
    · have inverse := mul_inv_cancel₀ (signed64_divisor_sum_nonzero b bb bz)
      simpa only [signed64Witness,bz,↓reduceIte,zero_add,one_mul,mul_one,ZMod.natCast_zmod_val,
        inverse,sub_self,mul_zero]
  all_goals
    by_cases sa : a < 9223372036854775808 <;> by_cases sb : b < 9223372036854775808 <;> by_cases bz : b=0 <;>
      norm_num [signed64Witness,signValue,sa,sb,bz]

theorem signed64_witness_outside (a b q r col : Nat) (outside : 47 ≤ col) :
    signed64Witness a b q r col = 0 := by
  dsimp only [signed64Witness]
  split <;> omega

end DivRemFV
