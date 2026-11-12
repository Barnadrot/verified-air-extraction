import DivRemFV.NegationWitness64
import DivRemFV.UnaryWitness
import DivRemFV.Negation
import DivRemFV.SignedSpec

namespace DivRemFV
open Generated

def digits32 (a : Nat) : Nat × Nat := (a / 65536,a % 65536)
def digits64 (a : Nat) : Nat × Nat × Nat × Nat :=
  (a / 281474976710656,a / 4294967296 % 65536,a / 65536 % 65536,a % 65536)

theorem pair_nat_limbs (h l : Nat) (hb : h < 65536) (lb : l < 65536) :
    (h,l) = digits32 (65536*h+l) := by
  apply Prod.ext <;> dsimp [digits32] <;> omega

theorem four_nat_limbs (h j k l : Nat)
    (hb : h < 65536) (jb : j < 65536) (kb : k < 65536) (lb : l < 65536) :
    (h,j,k,l) = digits64 (281474976710656*h+4294967296*j+65536*k+l) := by
  apply Prod.ext
  · dsimp [digits64]; omega
  · apply Prod.ext
    · dsimp [digits64]; omega
    · apply Prod.ext <;> dsimp [digits64] <;> omega

theorem absolute32_witness_value (a : Nat) (cap : a < 4294967296) :
    pairValue (absolute32Witness (a/65536) (a%65536)) 2 3 = magnitudeNat 32 a := by
  have hb : a/65536 < 65536 := by omega
  have lb : a%65536 < 65536 := Nat.mod_lt _ (by decide)
  have result := absolute32_result _ (absolute32_witness_bounds _ _ hb lb)
    (absolute32_witness_integer _ _ hb lb) (by change (1 : Nat) ≠ 0; decide)
  have input : pairValue (absolute32Witness (a/65536) (a%65536)) 0 1 = a := by
    dsimp [pairValue,absolute32Witness]; omega
  rw [input] at result
  simpa only [magnitudeNat,show 32-1=31 from rfl,show 2^31=2147483648 from rfl,
    show 2^32=4294967296 from rfl] using result

theorem negation32_witness_value (a : Nat) (cap : a < 4294967296) :
    pairValue (negation32Witness (a/65536) (a%65536)) 2 3 = negateNat 32 a := by
  have hb : a/65536 < 65536 := by omega
  have lb : a%65536 < 65536 := Nat.mod_lt _ (by decide)
  have result := negative32_result _ (negation32_witness_bounds _ _ hb lb)
    (negation32_witness_field _ _ hb lb) (negation32_witness_integer _ _ hb lb) (by change (1 : Nat) ≠ 0; decide)
  have input : pairValue (negation32Witness (a/65536) (a%65536)) 0 1 = a := by
    dsimp [pairValue,negation32Witness]; omega
  rw [input] at result
  simpa only [negateNat,show 2^32=4294967296 from rfl] using result

theorem absolute64_witness_value (a : Nat) (cap : a < 18446744073709551616) :
    let d := digits64 a
    wordValue (absolute64Witness d.1 d.2.1 d.2.2.1 d.2.2.2) 4 = magnitudeNat 64 a := by
  have hb : a/281474976710656 < 65536 := by omega
  have jb : a/4294967296%65536 < 65536 := Nat.mod_lt _ (by decide)
  have kb : a/65536%65536 < 65536 := Nat.mod_lt _ (by decide)
  have lb : a%65536 < 65536 := Nat.mod_lt _ (by decide)
  have result := absolute64_result _ (absolute64_witness_bounds _ _ _ _ hb jb kb lb)
    (absolute64_witness_integer _ _ _ _ hb jb kb lb) (by change (1 : Nat) ≠ 0; decide)
  have input : wordValue (absolute64Witness (a/281474976710656) (a/4294967296%65536)
      (a/65536%65536) (a%65536)) 0 = a := by
    dsimp [wordValue,absolute64Witness]
    have packing := split16_64 a
    omega
  rw [input] at result
  simpa only [digits64,magnitudeNat,show 64-1=63 from rfl,show 2^63=9223372036854775808 from rfl,
    show 2^64=18446744073709551616 from rfl] using result

theorem negation64_witness_value (a : Nat) (cap : a < 18446744073709551616) :
    let d := digits64 a
    wordValue (negation64Witness d.1 d.2.1 d.2.2.1 d.2.2.2) 4 = negateNat 64 a := by
  have hb : a/281474976710656 < 65536 := by omega
  have jb : a/4294967296%65536 < 65536 := Nat.mod_lt _ (by decide)
  have kb : a/65536%65536 < 65536 := Nat.mod_lt _ (by decide)
  have lb : a%65536 < 65536 := Nat.mod_lt _ (by decide)
  have result := negative64_result _ (negation64_witness_bounds _ _ _ _ hb jb kb lb)
    (negation64_witness_field _ _ _ _ hb jb kb lb) (negation64_witness_integer _ _ _ _ hb jb kb lb) (by change (1 : Nat) ≠ 0; decide)
  have input : wordValue (negation64Witness (a/281474976710656) (a/4294967296%65536)
      (a/65536%65536) (a%65536)) 0 = a := by
    dsimp [wordValue,negation64Witness]
    have packing := split16_64 a
    omega
  rw [input] at result
  simpa only [digits64,negateNat,show 2^64=18446744073709551616 from rfl] using result

theorem absolute32_witness_digits (a : Nat) (cap : a < 4294967296) :
    let v := absolute32Witness (a/65536) (a%65536)
    (v 2,v 3) = digits32 (magnitudeNat 32 a) := by
  have bounds := absolute32_witness_bounds (a/65536) (a%65536) (by omega) (Nat.mod_lt _ (by decide))
  have packed := pair_nat_limbs _ _ bounds.b2 bounds.b3
  change _ = digits32 (pairValue (absolute32Witness (a/65536) (a%65536)) 2 3) at packed
  rw [absolute32_witness_value a cap] at packed
  exact packed

theorem negation32_witness_digits (a : Nat) (cap : a < 4294967296) :
    let v := negation32Witness (a/65536) (a%65536)
    (v 2,v 3) = digits32 (negateNat 32 a) := by
  have bounds := negation32_witness_bounds (a/65536) (a%65536) (by omega) (Nat.mod_lt _ (by decide))
  have packed := pair_nat_limbs _ _ bounds.b2 bounds.b3
  change _ = digits32 (pairValue (negation32Witness (a/65536) (a%65536)) 2 3) at packed
  rw [negation32_witness_value a cap] at packed
  exact packed

theorem absolute64_witness_digits (a : Nat) (cap : a < 18446744073709551616) :
    let d := digits64 a
    let v := absolute64Witness d.1 d.2.1 d.2.2.1 d.2.2.2
    (v 4,v 5,v 6,v 7) = digits64 (magnitudeNat 64 a) := by
  have bounds := absolute64_witness_bounds (a/281474976710656) (a/4294967296%65536)
    (a/65536%65536) (a%65536) (by omega) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  have packed := four_nat_limbs _ _ _ _ bounds.b4 bounds.b5 bounds.b6 bounds.b7
  change _ = digits64 (wordValue (absolute64Witness (digits64 a).1 (digits64 a).2.1
    (digits64 a).2.2.1 (digits64 a).2.2.2) 4) at packed
  rw [absolute64_witness_value a cap] at packed
  exact packed

theorem negation64_witness_digits (a : Nat) (cap : a < 18446744073709551616) :
    let d := digits64 a
    let v := negation64Witness d.1 d.2.1 d.2.2.1 d.2.2.2
    (v 4,v 5,v 6,v 7) = digits64 (negateNat 64 a) := by
  have bounds := negation64_witness_bounds (a/281474976710656) (a/4294967296%65536)
    (a/65536%65536) (a%65536) (by omega) (Nat.mod_lt _ (by decide))
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  have packed := four_nat_limbs _ _ _ _ bounds.b4 bounds.b5 bounds.b6 bounds.b7
  change _ = digits64 (wordValue (negation64Witness (digits64 a).1 (digits64 a).2.1
    (digits64 a).2.2.1 (digits64 a).2.2.2) 4) at packed
  rw [negation64_witness_value a cap] at packed
  exact packed

end DivRemFV
