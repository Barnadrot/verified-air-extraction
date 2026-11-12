import DivRemFV.Unsigned64

namespace DivRemFV
open Generated

def wordValue (v : Nat → Nat) (start : Nat) : Nat :=
  281474976710656 * v start + 4294967296 * v (start + 1) +
    65536 * v (start + 2) + v (start + 3)

theorem wordInteger_ofNat (v : Nat → Nat) (start : Nat) :
    wordInteger (fun col => (v col : Int)) start = (wordValue v start : Int) := by
  simp only [wordInteger, wordValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

theorem unsigned64_nonzero_arithmetic (v : Nat → Nat)
    (h : IntegerEquations61 (fun col => (v col : Int)))
    (active : v 121 = 1) (nonzero : v 33 = 1) :
    wordValue v 0 = wordValue v 4 * wordValue v 8 + wordValue v 12 ∧
    wordValue v 4 = wordValue v 12 + wordValue v 16 + 1 := by
  have result := unsigned64_nonzero_integer (fun col => (v col : Int)) h
    (fun col => by change (0 : Int) ≤ (v col : Int); omega) (by simp [active]) (by simp [nonzero])
  simp only [wordInteger_ofNat] at result
  constructor
  · exact_mod_cast result.1
  · exact_mod_cast result.2

theorem unsigned64_result (v : Nat → Nat) (bounds : Bounds61 v)
    (fieldEquations : Equations61 (fun col => (v col : K)))
    (integerEquations : IntegerEquations61 (fun col => (v col : Int)))
    (active : v 121 ≠ 0) :
    wordValue v 8 = (if wordValue v 4 = 0 then 18446744073709551615 else wordValue v 0 / wordValue v 4) ∧
    wordValue v 12 = (if wordValue v 4 = 0 then wordValue v 0 else wordValue v 0 % wordValue v 4) := by
  have b8 := bounds.b8; have b9 := bounds.b9
  have b10 := bounds.b10; have b11 := bounds.b11
  have b33 := bounds.b33; have b121 := bounds.b121
  have activeOne : v 121 = 1 := by clear * - b121 active; omega
  have flags : v 33 = 0 ∨ v 33 = 1 := by clear * - b33; omega
  rcases flags with flagZero | flagOne
  · have gate : (v 121 : Int) = 1 := by simp [activeOne]
    have flag : (v 33 : Int) = 0 := by simp [flagZero]
    have guard := integerEquations.h11726
    simp only [gate, flag, zero_add, one_mul, mul_one, sub_zero] at guard
    have sum : v 4 + v 5 + v 6 + v 7 + 262140 = v 11 + v 10 + v 9 + v 8 := by
      clear * - guard; omega
    have divisorZero : wordValue v 4 = 0 := by
      dsimp [wordValue]; clear * - sum b8 b9 b10 b11; omega
    have q8 : v 8 = 65535 := by clear * - sum b8 b9 b10 b11; omega
    have q9 : v 9 = 65535 := by clear * - sum b8 b9 b10 b11; omega
    have q10 : v 10 = 65535 := by clear * - sum b8 b9 b10 b11; omega
    have q11 : v 11 = 65535 := by clear * - sum b8 b9 b10 b11; omega
    have low := integerEquations.h11727
    have next := integerEquations.h11728
    have next2 := integerEquations.h11729
    have high := integerEquations.h11730
    simp only [gate, flag, one_mul, mul_one, sub_zero] at low next next2 high
    simp only [divisorZero, ↓reduceIte]
    constructor
    · simp [wordValue, q8, q9, q10, q11]
    · dsimp [wordValue]; clear * - low next next2 high; omega
  · have divisorPositive : 0 < wordValue v 4 := by
      by_contra failure
      have zeros : v 4 = 0 ∧ v 5 = 0 ∧ v 6 = 0 ∧ v 7 = 0 := by
        dsimp [wordValue] at failure; clear * - failure; omega
      rcases zeros with ⟨z4,z5,z6,z7⟩
      have check := fieldEquations.h11725
      norm_num [activeOne, flagOne, z4, z5, z6, z7] at check
    have arithmetic := unsigned64_nonzero_arithmetic v integerEquations activeOne flagOne
    have result := (unsigned_hint_iff _ _ _ _ divisorPositive).1 ⟨wordValue v 16, arithmetic⟩
    simpa only [Nat.ne_of_gt divisorPositive, ↓reduceIte] using result

theorem unsigned64_air_sound_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 61).size) (accepted : ConstraintsHold tables Generated.constraints)
    (ranges : StaticRanges tables) (active : readCell tables 61 121 row ≠ 0) :
    let v := fun col => (readCell tables 61 col row).val
    wordValue v 8 = (if wordValue v 4 = 0 then 18446744073709551615 else wordValue v 0 / wordValue v 4) ∧
    wordValue v 12 = (if wordValue v 4 = 0 then wordValue v 0 else wordValue v 0 % wordValue v 4) := by
  apply unsigned64_result _ (bounds61 tables row inside accepted ranges)
    (equations61 tables row inside accepted) (integer_equations61 tables row inside accepted ranges)
  intro zero
  exact active (Fin.ext zero)

theorem unsigned64_air_sound (tables : Tables) (row : Nat)
    (inside : row < (tables 61).size) (accepted : ConstraintsHold tables Generated.constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 61 121 row ≠ 0) :
    let v := fun col => (readCell tables 61 col row).val
    wordValue v 8 = (if wordValue v 4 = 0 then 18446744073709551615 else wordValue v 0 / wordValue v 4) ∧
    wordValue v 12 = (if wordValue v 4 = 0 then wordValue v 0 else wordValue v 0 % wordValue v 4) := by
  exact unsigned64_air_sound_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active


def encodeFour (value : Nat) : Scalar × Scalar × Scalar × Scalar :=
  (encodeLimb (value / 281474976710656), encodeLimb (value / 4294967296),
    encodeLimb (value / 65536), encodeLimb value)

theorem four_limbs (a b c d : Scalar) (ha : a.val < 65536) (hb : b.val < 65536)
    (hc : c.val < 65536) (hd : d.val < 65536) :
    (a,b,c,d) = encodeFour (281474976710656*a.val + 4294967296*b.val + 65536*c.val + d.val) := by
  apply Prod.ext
  · apply Fin.ext
    dsimp [encodeFour, encodeLimb]
    omega
  · apply Prod.ext
    · apply Fin.ext
      dsimp [encodeFour, encodeLimb]
      omega
    · apply Prod.ext
      · apply Fin.ext
        dsimp [encodeFour, encodeLimb]
        omega
      · apply Fin.ext
        dsimp [encodeFour, encodeLimb]
        omega

theorem unsigned64_air_columns_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 61).size) (accepted : ConstraintsHold tables Generated.constraints)
    (ranges : StaticRanges tables) (active : readCell tables 61 121 row ≠ 0) :
    let v := fun col => (readCell tables 61 col row).val
    let q := if wordValue v 4 = 0 then 18446744073709551615 else wordValue v 0 / wordValue v 4
    let r := if wordValue v 4 = 0 then wordValue v 0 else wordValue v 0 % wordValue v 4
    (readCell tables 61 8 row,readCell tables 61 9 row,readCell tables 61 10 row,readCell tables 61 11 row) = encodeFour q ∧
    (readCell tables 61 12 row,readCell tables 61 13 row,readCell tables 61 14 row,readCell tables 61 15 row) = encodeFour r := by
  have bounds := bounds61 tables row inside accepted ranges
  have result := unsigned64_air_sound_of_ranges tables row inside accepted ranges active
  have q := four_limbs (readCell tables 61 8 row) (readCell tables 61 9 row)
    (readCell tables 61 10 row) (readCell tables 61 11 row) bounds.b8 bounds.b9 bounds.b10 bounds.b11
  have r := four_limbs (readCell tables 61 12 row) (readCell tables 61 13 row)
    (readCell tables 61 14 row) (readCell tables 61 15 row) bounds.b12 bounds.b13 bounds.b14 bounds.b15
  change _ = encodeFour (wordValue (fun col => (readCell tables 61 col row).val) 8) at q
  change _ = encodeFour (wordValue (fun col => (readCell tables 61 col row).val) 12) at r
  rw [result.1] at q
  rw [result.2] at r
  exact ⟨q,r⟩

theorem unsigned64_air_columns (tables : Tables) (row : Nat)
    (inside : row < (tables 61).size) (accepted : ConstraintsHold tables Generated.constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 61 121 row ≠ 0) :
    let v := fun col => (readCell tables 61 col row).val
    let q := if wordValue v 4 = 0 then 18446744073709551615 else wordValue v 0 / wordValue v 4
    let r := if wordValue v 4 = 0 then wordValue v 0 else wordValue v 0 % wordValue v 4
    (readCell tables 61 8 row,readCell tables 61 9 row,readCell tables 61 10 row,readCell tables 61 11 row) = encodeFour q ∧
    (readCell tables 61 12 row,readCell tables 61 13 row,readCell tables 61 14 row,readCell tables 61 15 row) = encodeFour r := by
  exact unsigned64_air_columns_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active


end DivRemFV
