import DivRemFV.Unsigned64Result

namespace DivRemFV
open Generated

theorem negative32_nonzero_arithmetic (v : Nat → Nat) (bounds : Bounds66 v)
    (h : IntegerEquations66 (fun col => (v col : Int)))
    (active : v 14 = 1) (nonzero : v 11 = 1) :
    pairValue v 2 3 + pairValue v 0 1 = 4294967296 := by
  have bit := bounds.b4
  have cases : v 4 = 0 ∨ v 4 = 1 := by clear * - bit; omega
  have ret : (v 14 : Int) = 1 := by simp [active]
  have flag : (v 11 : Int) = 1 := by simp [nonzero]
  rcases cases with positive | negative
  · have sign : (v 4 : Int) = 0 := by simp [positive]
    have guard := h.h12179
    have e0 := h.h12180
    have e1 := h.h12181
    have e2 := h.h12182
    have e3 := h.h12183
    simp only [ret, flag, sign, one_mul, mul_one, zero_add, sub_zero, neg_mul] at guard e0 e1 e2 e3
    have cap0 := bounds.b5
    have cap1 := bounds.b6
    have full0 : v 5 = 65535 := by
      clear * - guard cap0 cap1
      omega
    have full1 : v 6 = 65535 := by
      clear * - guard cap0 cap1
      omega
    have identity : (pairValue v 2 3 : Int) + (pairValue v 0 1 : Int) = 4294967296 := by
      simp only [pairValue, wordValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      simp only [full0, full1] at e0 e1 e2 e3
      linear_combination (1) * e0 + (-65536) * e1 + (1) * e2 + (65536) * e3
    exact_mod_cast identity
  · have sign : (v 4 : Int) = 1 := by simp [negative]
    have guard := h.h12184
    have e0 := h.h12185
    have e1 := h.h12186
    have e2 := h.h12187
    have e3 := h.h12188
    simp only [ret, flag, sign, one_mul, mul_one, zero_add, sub_zero, neg_mul] at guard e0 e1 e2 e3
    have cap0 := bounds.b7
    have cap1 := bounds.b8
    have full0 : v 7 = 65535 := by
      clear * - guard cap0 cap1
      omega
    have full1 : v 8 = 65535 := by
      clear * - guard cap0 cap1
      omega
    have identity : (pairValue v 2 3 : Int) + (pairValue v 0 1 : Int) = 4294967296 := by
      simp only [pairValue, wordValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      simp only [full0, full1] at e0 e1 e2 e3
      linear_combination (1) * e0 + (65536) * e1 + (1) * e2 + (65536) * e3
    exact_mod_cast identity

theorem negative32_result (v : Nat → Nat) (bounds : Bounds66 v)
    (fieldEquations : Equations66 (fun col => (v col : K)))
    (integerEquations : IntegerEquations66 (fun col => (v col : Int)))
    (active : v 14 ≠ 0) :
    pairValue v 2 3 = (if pairValue v 0 1 = 0 then 0 else 4294967296 - pairValue v 0 1) := by
  have br := bounds.b14
  have bf := bounds.b11
  have activeOne : v 14 = 1 := by clear * - br active; omega
  have cases : v 11 = 0 ∨ v 11 = 1 := by clear * - bf; omega
  rcases cases with flagZero | flagOne
  · have ret : (v 14 : Int) = 1 := by simp [activeOne]
    have flag : (v 11 : Int) = 0 := by simp [flagZero]
    have guard := integerEquations.h12179
    simp only [ret, flag, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, sub_zero] at guard
    have zeros : pairValue v 2 3 = 0 ∧ pairValue v 0 1 = 0 := by
      dsimp [pairValue, wordValue]
      clear * - guard
      omega
    simp [zeros.1, zeros.2]
  · have positive : 0 < pairValue v 0 1 := by
      by_contra failure
      have zeros : v 0 = 0 ∧ v 1 = 0 := by
        dsimp [pairValue, wordValue] at failure
        clear * - failure
        omega
      rcases zeros with ⟨z0,z1⟩
      have check := fieldEquations.h12178
      norm_num [activeOne, flagOne, z0, z1] at check
    have identity := negative32_nonzero_arithmetic v bounds integerEquations activeOne flagOne
    rw [if_neg (Nat.ne_of_gt positive)]
    clear * - identity
    omega

theorem negative32_air_sound_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 66).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 66 14 row ≠ 0) :
    let v := fun col => (readCell tables 66 col row).val
    pairValue v 2 3 = (if pairValue v 0 1 = 0 then 0 else 4294967296 - pairValue v 0 1) := by
  apply negative32_result _ (bounds66 tables row inside accepted ranges)
    (equations66 tables row inside accepted) (integer_equations66 tables row inside accepted ranges)
  intro zero
  exact active (Fin.ext zero)

theorem negative32_air_sound (tables : Tables) (row : Nat)
    (inside : row < (tables 66).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 66 14 row ≠ 0) :
    let v := fun col => (readCell tables 66 col row).val
    pairValue v 2 3 = (if pairValue v 0 1 = 0 then 0 else 4294967296 - pairValue v 0 1) := by
  exact negative32_air_sound_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active

theorem negative64_nonzero_arithmetic (v : Nat → Nat) (bounds : Bounds65 v)
    (h : IntegerEquations65 (fun col => (v col : Int)))
    (active : v 28 = 1) (nonzero : v 21 = 1) :
    wordValue v 4 + wordValue v 0 = 18446744073709551616 := by
  have bit := bounds.b8
  have cases : v 8 = 0 ∨ v 8 = 1 := by clear * - bit; omega
  have ret : (v 28 : Int) = 1 := by simp [active]
  have flag : (v 21 : Int) = 1 := by simp [nonzero]
  rcases cases with positive | negative
  · have sign : (v 8 : Int) = 0 := by simp [positive]
    have guard := h.h12128
    have e0 := h.h12129
    have e1 := h.h12130
    have e2 := h.h12131
    have e3 := h.h12132
    have e4 := h.h12133
    have e5 := h.h12134
    have e6 := h.h12135
    have e7 := h.h12136
    simp only [ret, flag, sign, one_mul, mul_one, zero_add, sub_zero, neg_mul] at guard e0 e1 e2 e3 e4 e5 e6 e7
    have cap0 := bounds.b9
    have cap1 := bounds.b10
    have cap2 := bounds.b11
    have cap3 := bounds.b12
    have full0 : v 9 = 65535 := by
      clear * - guard cap0 cap1 cap2 cap3
      omega
    have full1 : v 10 = 65535 := by
      clear * - guard cap0 cap1 cap2 cap3
      omega
    have full2 : v 11 = 65535 := by
      clear * - guard cap0 cap1 cap2 cap3
      omega
    have full3 : v 12 = 65535 := by
      clear * - guard cap0 cap1 cap2 cap3
      omega
    have identity : (wordValue v 4 : Int) + (wordValue v 0 : Int) = 18446744073709551616 := by
      simp only [pairValue, wordValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      simp only [full0, full1, full2, full3] at e0 e1 e2 e3 e4 e5 e6 e7
      linear_combination (1) * e0 + (-65536) * e1 + (-4294967296) * e2 + (-281474976710656) * e3 + (1) * e4 + (65536) * e5 + (4294967296) * e6 + (281474976710656) * e7
    exact_mod_cast identity
  · have sign : (v 8 : Int) = 1 := by simp [negative]
    have guard := h.h12137
    have e0 := h.h12138
    have e1 := h.h12139
    have e2 := h.h12140
    have e3 := h.h12141
    have e4 := h.h12142
    have e5 := h.h12143
    have e6 := h.h12144
    have e7 := h.h12145
    simp only [ret, flag, sign, one_mul, mul_one, zero_add, sub_zero, neg_mul] at guard e0 e1 e2 e3 e4 e5 e6 e7
    have cap0 := bounds.b13
    have cap1 := bounds.b14
    have cap2 := bounds.b15
    have cap3 := bounds.b16
    have full0 : v 13 = 65535 := by
      clear * - guard cap0 cap1 cap2 cap3
      omega
    have full1 : v 14 = 65535 := by
      clear * - guard cap0 cap1 cap2 cap3
      omega
    have full2 : v 15 = 65535 := by
      clear * - guard cap0 cap1 cap2 cap3
      omega
    have full3 : v 16 = 65535 := by
      clear * - guard cap0 cap1 cap2 cap3
      omega
    have identity : (wordValue v 4 : Int) + (wordValue v 0 : Int) = 18446744073709551616 := by
      simp only [pairValue, wordValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      simp only [full0, full1, full2, full3] at e0 e1 e2 e3 e4 e5 e6 e7
      linear_combination (1) * e0 + (65536) * e1 + (4294967296) * e2 + (281474976710656) * e3 + (1) * e4 + (65536) * e5 + (4294967296) * e6 + (281474976710656) * e7
    exact_mod_cast identity

theorem negative64_result (v : Nat → Nat) (bounds : Bounds65 v)
    (fieldEquations : Equations65 (fun col => (v col : K)))
    (integerEquations : IntegerEquations65 (fun col => (v col : Int)))
    (active : v 28 ≠ 0) :
    wordValue v 4 = (if wordValue v 0 = 0 then 0 else 18446744073709551616 - wordValue v 0) := by
  have br := bounds.b28
  have bf := bounds.b21
  have activeOne : v 28 = 1 := by clear * - br active; omega
  have cases : v 21 = 0 ∨ v 21 = 1 := by clear * - bf; omega
  rcases cases with flagZero | flagOne
  · have ret : (v 28 : Int) = 1 := by simp [activeOne]
    have flag : (v 21 : Int) = 0 := by simp [flagZero]
    have guard := integerEquations.h12128
    simp only [ret, flag, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, sub_zero] at guard
    have zeros : wordValue v 4 = 0 ∧ wordValue v 0 = 0 := by
      dsimp [pairValue, wordValue]
      clear * - guard
      omega
    simp [zeros.1, zeros.2]
  · have positive : 0 < wordValue v 0 := by
      by_contra failure
      have zeros : v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
        dsimp [pairValue, wordValue] at failure
        clear * - failure
        omega
      rcases zeros with ⟨z0,z1,z2,z3⟩
      have check := fieldEquations.h12127
      norm_num [activeOne, flagOne, z0, z1, z2, z3] at check
    have identity := negative64_nonzero_arithmetic v bounds integerEquations activeOne flagOne
    rw [if_neg (Nat.ne_of_gt positive)]
    clear * - identity
    omega

theorem negative64_air_sound_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 65).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 65 28 row ≠ 0) :
    let v := fun col => (readCell tables 65 col row).val
    wordValue v 4 = (if wordValue v 0 = 0 then 0 else 18446744073709551616 - wordValue v 0) := by
  apply negative64_result _ (bounds65 tables row inside accepted ranges)
    (equations65 tables row inside accepted) (integer_equations65 tables row inside accepted ranges)
  intro zero
  exact active (Fin.ext zero)

theorem negative64_air_sound (tables : Tables) (row : Nat)
    (inside : row < (tables 65).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 65 28 row ≠ 0) :
    let v := fun col => (readCell tables 65 col row).val
    wordValue v 4 = (if wordValue v 0 = 0 then 0 else 18446744073709551616 - wordValue v 0) := by
  exact negative64_air_sound_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active

end DivRemFV
