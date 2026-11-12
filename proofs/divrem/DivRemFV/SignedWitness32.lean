import DivRemFV.UnaryDigits
import DivRemFV.Generated.WitnessRows

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DivRemFV
open Generated

def signed32Witness (a b q r col : Nat) : Nat :=
  let sa := signValue 32 a
  let sb := signValue 32 b
  let qo := if b=0 then 4294967295 else if sa=sb then q else negateNat 32 q
  let ro := if b=0 then a else if sa=0 then r else negateNat 32 r
  match col with
  | 0 => a/65536
  | 1 => a%65536
  | 2 => b/65536
  | 3 => b%65536
  | 4 => qo/65536
  | 5 => qo%65536
  | 6 => ro/65536
  | 7 => ro%65536
  | 8 => q/65536
  | 9 => q%65536
  | 10 => r/65536
  | 11 => r%65536
  | 12 => sa
  | 13 => magnitudeNat 32 a/65536
  | 14 => magnitudeNat 32 a%65536
  | 15 => magnitudeNat 32 b/65536
  | 16 => magnitudeNat 32 b%65536
  | 17 => sb
  | 18 => a/65536%32768
  | 19 => a%65536
  | 20 => b/65536%32768
  | 21 => b%65536
  | 22 => if b=0 then 0 else 1
  | 23 => 1
  | 24 => if b≠0 ∧ sa≠sb then 1 else 0
  | 25 => if b≠0 ∧ sa=1 then 1 else 0
  | 26 => (((b/65536 : Nat) : K)+((b%65536 : Nat) : K))⁻¹ |>.val
  | _ => 0

theorem signed32_witness_bounds (a b q r : Nat)
    (ab : a < 4294967296) (bb : b < 4294967296)
    (qb : q < 4294967296) (rb : r < 4294967296) : Bounds64 (signed32Witness a b q r) := by
  constructor <;> simp only [signed32Witness,signValue,magnitudeNat,negateNat] <;>
    norm_num only <;> (try split_ifs) <;> omega

theorem signed32_witness_integer (a b q r : Nat)
    (ab : a < 4294967296) (bb : b < 4294967296) :
    IntegerEquations64 (fun col => (signed32Witness a b q r col : Int)) := by
  by_cases sa : a < 2147483648 <;> by_cases sb : b < 2147483648 <;> by_cases bz : b=0 <;>
    constructor <;> norm_num [signed32Witness,signValue,sa,sb,bz] <;> omega

theorem signed32_witness_field (a b q r : Nat)
    (ab : a < 4294967296) (bb : b < 4294967296) :
    Equations64 (fun col => (signed32Witness a b q r col : K)) := by
  apply integer_to_field64 _ (signed32_witness_integer a b q r ab bb)
  · by_cases bz : b=0
    · subst b; norm_num [signed32Witness]
    · have nonzero : ((b/65536 : Nat) : K)+((b%65536 : Nat) : K) ≠ 0 := by
        intro eq
        have cast : ((b/65536+b%65536 : Nat) : K) = 0 := by simpa only [Nat.cast_add] using eq
        have value := lift_field_equality _ 0 (by dsimp [fieldModulus]; omega) (by decide) cast
        omega
      have inverse := mul_inv_cancel₀ nonzero
      simpa only [signed32Witness,zero_add,one_mul,mul_one,ZMod.natCast_zmod_val,
        inverse,sub_self,mul_zero]
  · by_cases bz : b=0
    · subst b; norm_num [signed32Witness]
    · have nonzero : ((b/65536 : Nat) : K)+((b%65536 : Nat) : K) ≠ 0 := by
        intro eq
        have cast : ((b/65536+b%65536 : Nat) : K) = 0 := by simpa only [Nat.cast_add] using eq
        have value := lift_field_equality _ 0 (by dsimp [fieldModulus]; omega) (by decide) cast
        omega
      have inverse := mul_inv_cancel₀ nonzero
      simpa only [signed32Witness,bz,↓reduceIte,zero_add,one_mul,mul_one,ZMod.natCast_zmod_val,
        inverse,sub_self,mul_zero]
  all_goals
    by_cases sa : a < 2147483648 <;> by_cases sb : b < 2147483648 <;> by_cases bz : b=0 <;>
      norm_num [signed32Witness,signValue,sa,sb,bz]

theorem signed32_witness_outside (a b q r col : Nat) (outside : 27 ≤ col) :
    signed32Witness a b q r col = 0 := by
  dsimp only [signed32Witness]
  split <;> omega

end DivRemFV
