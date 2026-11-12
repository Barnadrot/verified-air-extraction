import DivRemFV.UnsignedWitness32
import DivRemFV.Generated.ReverseRows

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

theorem booleanNat_integer (value : Nat) (bounded : value < 2) :
    (value : Int) * (value : Int) - (value : Int) = 0 := by
  have cases : value = 0 ∨ value = 1 := by omega
  rcases cases with rfl | rfl <;> norm_num

theorem unsigned32_nonzero_witness_integer (a b q r w : Nat)
    (aBound : a < 4294967296) (bBound : b < 4294967296)
    (qBound : q < 4294967296) (rBound : r < 4294967296) (wBound : w < 4294967296)
    (identity : a = q * b + r) (remainderBound : b = r + w + 1) :
    IntegerEquations63 (fun col => (unsigned32NonzeroWitness a b q r w col : Int)) := by
  have productBound : q * b < 4294967296 := by omega
  have bounds := unsigned32_nonzero_witness_bounds a b q r w aBound bBound qBound rBound wBound identity
  have bit19 := booleanNat_integer (unsigned32NonzeroWitness a b q r w 19) bounds.b19
  have bit24 := booleanNat_integer (unsigned32NonzeroWitness a b q r w 24) bounds.b24
  have bit45 := booleanNat_integer (unsigned32NonzeroWitness a b q r w 45) bounds.b45
  have bit49 := booleanNat_integer (unsigned32NonzeroWitness a b q r w 49) bounds.b49
  have bit50 := booleanNat_integer (unsigned32NonzeroWitness a b q r w 50) bounds.b50
  norm_num [unsigned32NonzeroWitness] at bit19 bit24 bit45 bit49 bit50
  have p00 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial32 q b 0 0) 32768)
  have p01 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial32 q b 0 1) 32768)
  have p02 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial32 q b 0 2) 32768)
  have p10 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial32 q b 1 0) 32768)
  have p11 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial32 q b 1 1) 32768)
  have p12 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial32 q b 1 2) 32768)
  have p20 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial32 q b 2 0) 32768)
  have p21 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial32 q b 2 1) 32768)
  norm_num [partial32, digit15] at p00 p01 p02 p10 p11 p12 p20 p21
  have merged := product32_merge q b productBound
  norm_num [partial32, digit15] at merged
  obtain ⟨overflowLow, overflowHigh⟩ := product32_no_overflow q b productBound
  unfold overflowLow32 at overflowLow
  unfold overflowHigh32 at overflowHigh
  have middleDefinition : middle32 q b = partial32 q b 0 0 / 32768 +
      partial32 q b 0 1 % 32768 + partial32 q b 1 0 % 32768 := rfl
  have nextDefinition : next32 q b = partial32 q b 0 1 / 32768 +
      partial32 q b 0 2 % 32768 + partial32 q b 1 0 / 32768 +
      partial32 q b 1 1 % 32768 + partial32 q b 2 0 % 32768 := rfl
  constructor
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - p00
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - p01
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - p02
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - p10
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - p11
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - p12
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - p20
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - p21
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - middleDefinition
    have natural : middle32 q b % 32768 % 2 + 2 * (middle32 q b % 32768 / 2) +
        32768 * (middle32 q b / 32768) = partial32 q b 0 0 / 32768 +
          partial32 q b 0 1 % 32768 + partial32 q b 1 0 % 32768 := by omega
    have cast := congrArg (fun value : Nat => (value : Int)) natural
    push_cast at cast
    norm_num only [unsigned32NonzeroWitness, one_mul, mul_one, zero_add]
    omega
  · clear * - nextDefinition
    have natural : next32 q b + middle32 q b / 32768 = partial32 q b 0 1 / 32768 +
        partial32 q b 0 2 % 32768 + partial32 q b 1 0 / 32768 +
        partial32 q b 1 1 % 32768 + partial32 q b 2 0 % 32768 + middle32 q b / 32768 := by omega
    have cast := congrArg (fun value : Nat => (value : Int)) natural
    push_cast at cast
    norm_num only [unsigned32NonzeroWitness, one_mul, mul_one, zero_add, Nat.cast_add]
    omega
  · clear * - overflowLow overflowHigh
    have lowCast := congrArg (fun value : Nat => (value : Int)) overflowLow
    have highCast := congrArg (fun value : Nat => (value : Int)) overflowHigh
    push_cast at lowCast highCast
    norm_num only [unsigned32NonzeroWitness, one_mul, mul_one, zero_add, sub_zero, Nat.cast_zero]
    omega
  · clear * - merged
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - merged
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - identity
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - identity
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - remainderBound
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - remainderBound
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - bit19
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - bit24
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - bit45
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - bit49
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · clear * - bit50
    norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned32NonzeroWitness, partial32, digit15] <;>
      first | assumption | omega

theorem unsigned32_nonzero_witness_field (a b q r w : Nat)
    (aBound : a < 4294967296) (bBound : b < 4294967296)
    (qBound : q < 4294967296) (rBound : r < 4294967296) (wBound : w < 4294967296)
    (identity : a = q * b + r) (remainderBound : b = r + w + 1) :
    Equations63 (fun col => (unsigned32NonzeroWitness a b q r w col : K)) := by
  have integer := unsigned32_nonzero_witness_integer a b q r w
    aBound bBound qBound rBound wBound identity remainderBound
  have sumBound : b / 65536 + b % 65536 < fieldModulus := by
    dsimp [fieldModulus]
    omega
  have sumPositive : 0 < b / 65536 + b % 65536 := by omega
  have nonzero : ((b / 65536 : Nat) : K) + ((b % 65536 : Nat) : K) ≠ 0 := by
    intro zero
    have cast : ((b / 65536 + b % 65536 : Nat) : K) = 0 := by
      simpa only [Nat.cast_add] using zero
    have value := lift_field_equality _ 0 sumBound (by decide) cast
    omega
  have inverse := mul_inv_cancel₀ nonzero
  apply integer_to_field63 _ integer
  · simpa only [unsigned32NonzeroWitness, zero_add, one_mul, mul_one,
      ZMod.natCast_zmod_val, inverse, sub_self, mul_zero]
  · simpa only [unsigned32NonzeroWitness, zero_add, one_mul, mul_one,
      ZMod.natCast_zmod_val, inverse, sub_self, mul_zero]

end DivRemFV
