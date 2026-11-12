import DivRemFV.UnsignedWitness64
import DivRemFV.UnsignedNonzero32

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

theorem recompose_two_radices (value base minor : Nat) :
    value % base % minor + minor * (value % base / minor) + base * (value / base) = value := by
  rw [Nat.mod_add_div (value % base) minor, Nat.mod_add_div value base]

theorem unsigned64_nonzero_witness_integer (a b q r w : Nat)
    (aBound : a < 18446744073709551616) (bBound : b < 18446744073709551616)
    (qBound : q < 18446744073709551616) (rBound : r < 18446744073709551616)
    (wBound : w < 18446744073709551616)
    (identity : a = q * b + r) (remainderBound : b = r + w + 1) :
    IntegerEquations61 (fun col => (unsigned64NonzeroWitness a b q r w col : Int)) := by
  have productBound : q * b < 18446744073709551616 := by omega
  have bounds := unsigned64_nonzero_witness_bounds a b q r w aBound bBound qBound rBound wBound identity
  have bit35 := booleanNat_integer (unsigned64NonzeroWitness a b q r w 35) bounds.b35
  have bit46 := booleanNat_integer (unsigned64NonzeroWitness a b q r w 46) bounds.b46
  have bit105 := booleanNat_integer (unsigned64NonzeroWitness a b q r w 105) bounds.b105
  have bit115 := booleanNat_integer (unsigned64NonzeroWitness a b q r w 115) bounds.b115
  have bit116 := booleanNat_integer (unsigned64NonzeroWitness a b q r w 116) bounds.b116
  have bit117 := booleanNat_integer (unsigned64NonzeroWitness a b q r w 117) bounds.b117
  have bit118 := booleanNat_integer (unsigned64NonzeroWitness a b q r w 118) bounds.b118
  have bit119 := booleanNat_integer (unsigned64NonzeroWitness a b q r w 119) bounds.b119
  have bit120 := booleanNat_integer (unsigned64NonzeroWitness a b q r w 120) bounds.b120
  norm_num [unsigned64NonzeroWitness] at bit35 bit46 bit105 bit115 bit116 bit117 bit118 bit119 bit120
  have p00 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 0 0) 32768)
  have p01 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 0 1) 32768)
  have p02 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 0 2) 32768)
  have p03 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 0 3) 32768)
  have p04 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 0 4) 32768)
  have p10 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 1 0) 32768)
  have p11 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 1 1) 32768)
  have p12 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 1 2) 32768)
  have p13 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 1 3) 32768)
  have p14 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 1 4) 32768)
  have p20 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 2 0) 32768)
  have p21 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 2 1) 32768)
  have p22 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 2 2) 32768)
  have p23 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 2 3) 32768)
  have p24 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 2 4) 32768)
  have p30 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 3 0) 32768)
  have p31 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 3 1) 32768)
  have p32 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 3 2) 32768)
  have p33 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 3 3) 32768)
  have p34 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 3 4) 32768)
  have p40 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 4 0) 32768)
  have p41 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 4 1) 32768)
  have p42 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 4 2) 32768)
  have p43 := congrArg (fun value : Nat => (value : Int))
    (Nat.mod_add_div (partial64 q b 4 3) 32768)
  norm_num [partial64, digit15] at p00 p01 p02 p03 p04 p10 p11 p12 p13 p14 p20 p21 p22 p23 p24 p30 p31 p32 p33 p34 p40 p41 p42 p43
  have d0 : coefficient64 q b 0 = partial64 q b 0 0 % 32768 := rfl
  have d1 : coefficient64 q b 1 = partial64 q b 0 0 / 32768 + partial64 q b 0 1 % 32768 + partial64 q b 1 0 % 32768 := rfl
  have d2 : coefficient64 q b 2 = partial64 q b 0 1 / 32768 + partial64 q b 0 2 % 32768 + partial64 q b 1 0 / 32768 + partial64 q b 1 1 % 32768 + partial64 q b 2 0 % 32768 := rfl
  have d3 : coefficient64 q b 3 = partial64 q b 0 2 / 32768 + partial64 q b 0 3 % 32768 + partial64 q b 1 1 / 32768 + partial64 q b 1 2 % 32768 + partial64 q b 2 0 / 32768 + partial64 q b 2 1 % 32768 + partial64 q b 3 0 % 32768 := rfl
  have d4 : coefficient64 q b 4 = partial64 q b 0 3 / 32768 + partial64 q b 0 4 % 32768 + partial64 q b 1 2 / 32768 + partial64 q b 1 3 % 32768 + partial64 q b 2 1 / 32768 + partial64 q b 2 2 % 32768 + partial64 q b 3 0 / 32768 + partial64 q b 3 1 % 32768 + partial64 q b 4 0 % 32768 := rfl
  have m0 : merged64 q b 0 = coefficient64 q b 0 := rfl
  have m1 : merged64 q b 1 = coefficient64 q b 1 + merged64 q b 0 / 32768 := rfl
  have m2 : merged64 q b 2 = coefficient64 q b 2 + merged64 q b 1 / 32768 := rfl
  have m3 : merged64 q b 3 = coefficient64 q b 3 + merged64 q b 2 / 32768 := rfl
  have m4 : merged64 q b 4 = coefficient64 q b 4 + merged64 q b 3 / 32768 := rfl
  have c0 : coefficient64 q b 0 < 32768 := Nat.mod_lt _ (by decide)
  have merged := product64_merge q b productBound
  rw [d0] at merged
  norm_num [partial64, digit15] at merged
  obtain ⟨o5,o6,o7,o8⟩ := product64_no_overflow q b productBound
  dsimp only [coefficient64] at o5 o6 o7 o8
  constructor
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - qBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p00
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p01
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p02
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p03
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p04
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p10
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p11
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p12
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p13
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p14
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p20
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p21
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p22
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p23
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p24
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p30
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p31
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p32
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p33
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p34
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p40
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p41
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p42
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - p43
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - d1 m1 m0 c0
    have recompose := recompose_two_radices (merged64 q b 1) 32768 2
    have natural : merged64 q b 1 % 32768 % 2 + 2 * (merged64 q b 1 % 32768 / 2) + 32768 * (merged64 q b 1 / 32768) = partial64 q b 0 0 / 32768 + partial64 q b 0 1 % 32768 + partial64 q b 1 0 % 32768 := by omega
    have cast := congrArg (fun value : Nat => (value : Int)) natural
    push_cast at cast
    norm_num only [unsigned64NonzeroWitness, one_mul, mul_one, zero_add, Nat.cast_add]
    omega
  · clear * - d2 m2
    have recompose := recompose_two_radices (merged64 q b 2) 32768 4
    have natural : merged64 q b 2 % 32768 % 4 + 4 * (merged64 q b 2 % 32768 / 4) + 32768 * (merged64 q b 2 / 32768) = partial64 q b 0 1 / 32768 + partial64 q b 0 2 % 32768 + partial64 q b 1 0 / 32768 + partial64 q b 1 1 % 32768 + partial64 q b 2 0 % 32768 + merged64 q b 1 / 32768 := by omega
    have cast := congrArg (fun value : Nat => (value : Int)) natural
    push_cast at cast
    norm_num only [unsigned64NonzeroWitness, one_mul, mul_one, zero_add, Nat.cast_add]
    omega
  · clear * - d3 m3
    have recompose := recompose_two_radices (merged64 q b 3) 32768 8
    have natural : merged64 q b 3 % 32768 % 8 + 8 * (merged64 q b 3 % 32768 / 8) + 32768 * (merged64 q b 3 / 32768) = partial64 q b 0 2 / 32768 + partial64 q b 0 3 % 32768 + partial64 q b 1 1 / 32768 + partial64 q b 1 2 % 32768 + partial64 q b 2 0 / 32768 + partial64 q b 2 1 % 32768 + partial64 q b 3 0 % 32768 + merged64 q b 2 / 32768 := by omega
    have cast := congrArg (fun value : Nat => (value : Int)) natural
    push_cast at cast
    norm_num only [unsigned64NonzeroWitness, one_mul, mul_one, zero_add, Nat.cast_add]
    omega
  · clear * - d4 m4
    have natural : merged64 q b 4 = partial64 q b 0 3 / 32768 + partial64 q b 0 4 % 32768 + partial64 q b 1 2 / 32768 + partial64 q b 1 3 % 32768 + partial64 q b 2 1 / 32768 + partial64 q b 2 2 % 32768 + partial64 q b 3 0 / 32768 + partial64 q b 3 1 % 32768 + partial64 q b 4 0 % 32768 + merged64 q b 3 / 32768 := by omega
    have cast := congrArg (fun value : Nat => (value : Int)) natural
    push_cast at cast
    norm_num only [unsigned64NonzeroWitness, one_mul, mul_one, zero_add, Nat.cast_add]
    omega
  · clear * - o5 o6 o7 o8
    have h5 := congrArg (fun value : Nat => (value : Int)) o5
    have h6 := congrArg (fun value : Nat => (value : Int)) o6
    have h7 := congrArg (fun value : Nat => (value : Int)) o7
    have h8 := congrArg (fun value : Nat => (value : Int)) o8
    push_cast at h5 h6 h7 h8
    norm_num only [unsigned64NonzeroWitness, one_mul, mul_one, zero_add, Nat.cast_zero, sub_zero]
    omega
  · clear * - merged
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - merged
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - merged
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - merged
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - identity
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - identity
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - identity
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - identity
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - remainderBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - remainderBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - remainderBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - remainderBound
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bit35
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bit46
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bit105
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bit115
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bit116
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bit117
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bit118
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bit119
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · clear * - bit120
    norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega
  · norm_num [unsigned64NonzeroWitness, partial64, digit15] <;>
      first | assumption | omega

theorem unsigned64_nonzero_witness_field (a b q r w : Nat)
    (aBound : a < 18446744073709551616) (bBound : b < 18446744073709551616)
    (qBound : q < 18446744073709551616) (rBound : r < 18446744073709551616)
    (wBound : w < 18446744073709551616)
    (identity : a = q * b + r) (remainderBound : b = r + w + 1) :
    Equations61 (fun col => (unsigned64NonzeroWitness a b q r w col : K)) := by
  have integer := unsigned64_nonzero_witness_integer a b q r w
    aBound bBound qBound rBound wBound identity remainderBound
  let total := b / 281474976710656 + b / 4294967296 % 65536 + b / 65536 % 65536 + b % 65536
  have totalBound : total < fieldModulus := by
    dsimp [total,fieldModulus]
    omega
  have totalPositive : 0 < total := by
    have packing := split16_64 b
    dsimp [total]
    clear * - packing remainderBound
    omega
  have nonzero : ((b / 281474976710656 : Nat) : K) + ((b / 4294967296 % 65536 : Nat) : K) +
      ((b / 65536 % 65536 : Nat) : K) + ((b % 65536 : Nat) : K) ≠ 0 := by
    intro zero
    have cast : (total : K) = 0 := by simpa only [total,Nat.cast_add] using zero
    have value := lift_field_equality _ 0 totalBound (by decide) cast
    omega
  have inverse := mul_inv_cancel₀ nonzero
  apply integer_to_field61 _ integer
  · simpa only [unsigned64NonzeroWitness,zero_add,one_mul,mul_one,
      ZMod.natCast_zmod_val,inverse,sub_self,mul_zero]
  · simpa only [unsigned64NonzeroWitness,zero_add,one_mul,mul_one,
      ZMod.natCast_zmod_val,inverse,sub_self,mul_zero]

end DivRemFV

