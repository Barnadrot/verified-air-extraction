import DivRemFV.Unsigned64Result

namespace DivRemFV
open Generated

theorem absolute32_result (v : Nat → Nat) (bounds : Bounds56 v)
    (h : IntegerEquations56 (fun col => (v col : Int))) (active : v 13 ≠ 0) :
    pairValue v 2 3 = (if pairValue v 0 1 < 2147483648 then pairValue v 0 1 else 4294967296 - pairValue v 0 1) := by
  have b1 := bounds.b1; have b4 := bounds.b4
  have b7 := bounds.b7; have b8 := bounds.b8
  have b9 := bounds.b9; have b13 := bounds.b13
  have activeOne : v 13 = 1 := by clear * - b13 active; omega
  have ret : (v 13 : Int) = 1 := by simp [activeOne]
  have splitHigh := h.h11196
  simp only [ret, one_mul, zero_add] at splitHigh
  have cases : v 4 = 0 ∨ v 4 = 1 := by clear * - b4; omega
  rcases cases with positive | negative
  · have sign : (v 4 : Int) = 0 := by simp [positive]
    have low := h.h11197
    have high := h.h11198
    simp only [ret, sign, one_mul, mul_one, sub_zero] at low high
    have threshold : pairValue v 0 1 < 2147483648 := by
      dsimp [pairValue]; clear * - b1 b9 splitHigh sign; omega
    rw [if_pos threshold]
    dsimp [pairValue]; clear * - low high; omega
  · have sign : (v 4 : Int) = 1 := by simp [negative]
    have threshold : ¬pairValue v 0 1 < 2147483648 := by
      dsimp [pairValue]; clear * - splitHigh sign; omega
    have complement := h.h11199
    have subtractLow := h.h11200
    have subtractHigh := h.h11201
    have addLow := h.h11202
    have addHigh := h.h11203
    simp only [ret, sign, one_mul, mul_one, zero_add, neg_mul] at complement subtractLow subtractHigh addLow addHigh
    have full7 : v 7 = 65535 := by clear * - complement b7 b8; omega
    have full8 : v 8 = 65535 := by clear * - complement b7 b8; omega
    have identity : (pairValue v 2 3 : Int) + (pairValue v 0 1 : Int) = 4294967296 := by
      simp only [pairValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      simp only [full7, full8] at subtractLow subtractHigh
      linear_combination subtractLow + 65536 * subtractHigh + addLow + 65536 * addHigh
    have natural : pairValue v 2 3 + pairValue v 0 1 = 4294967296 := by exact_mod_cast identity
    rw [if_neg threshold]
    clear * - natural; omega

theorem absolute64_result (v : Nat → Nat) (bounds : Bounds55 v)
    (h : IntegerEquations55 (fun col => (v col : Int))) (active : v 27 ≠ 0) :
    wordValue v 4 = (if wordValue v 0 < 9223372036854775808 then wordValue v 0 else 18446744073709551616 - wordValue v 0) := by
  have b1 := bounds.b1; have b2 := bounds.b2; have b3 := bounds.b3
  have b8 := bounds.b8; have b17 := bounds.b17; have b27 := bounds.b27
  have b13 := bounds.b13; have b14 := bounds.b14; have b15 := bounds.b15; have b16 := bounds.b16
  have activeOne : v 27 = 1 := by clear * - b27 active; omega
  have ret : (v 27 : Int) = 1 := by simp [activeOne]
  have splitHigh := h.h11153
  simp only [ret, one_mul, zero_add] at splitHigh
  have cases : v 8 = 0 ∨ v 8 = 1 := by clear * - b8; omega
  rcases cases with positive | negative
  · have sign : (v 8 : Int) = 0 := by simp [positive]
    have lo := h.h11154; have next := h.h11155
    have next2 := h.h11156; have hi := h.h11157
    simp only [ret, sign, one_mul, mul_one, sub_zero] at lo next next2 hi
    have threshold : wordValue v 0 < 9223372036854775808 := by
      dsimp [wordValue]; clear * - b1 b2 b3 b17 splitHigh sign; omega
    rw [if_pos threshold]
    dsimp [wordValue]; clear * - lo next next2 hi; omega
  · have sign : (v 8 : Int) = 1 := by simp [negative]
    have threshold : ¬wordValue v 0 < 9223372036854775808 := by
      dsimp [wordValue]; clear * - splitHigh sign; omega
    have complement := h.h11158
    have s0 := h.h11159; have s1 := h.h11160
    have s2 := h.h11161; have s3 := h.h11162
    have c0 := h.h11163; have c1 := h.h11164
    have c2 := h.h11165; have c3 := h.h11166
    simp only [ret, sign, one_mul, mul_one, zero_add, neg_mul] at complement s0 s1 s2 s3 c0 c1 c2 c3
    have full13 : v 13 = 65535 := by clear * - complement b13 b14 b15 b16; omega
    have full14 : v 14 = 65535 := by clear * - complement b13 b14 b15 b16; omega
    have full15 : v 15 = 65535 := by clear * - complement b13 b14 b15 b16; omega
    have full16 : v 16 = 65535 := by clear * - complement b13 b14 b15 b16; omega
    have identity : (wordValue v 4 : Int) + (wordValue v 0 : Int) = 18446744073709551616 := by
      simp only [wordValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      simp only [full13, full14, full15, full16] at s0 s1 s2 s3
      linear_combination s0 + 65536*s1 + 4294967296*s2 + 281474976710656*s3 +
        c0 + 65536*c1 + 4294967296*c2 + 281474976710656*c3
    have natural : wordValue v 4 + wordValue v 0 = 18446744073709551616 := by exact_mod_cast identity
    rw [if_neg threshold]
    clear * - natural; omega

theorem absolute32_air_sound_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 56).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 56 13 row ≠ 0) :
    let v := fun col => (readCell tables 56 col row).val
    pairValue v 2 3 = (if pairValue v 0 1 < 2147483648 then pairValue v 0 1 else 4294967296 - pairValue v 0 1) := by
  apply absolute32_result _ (bounds56 tables row inside accepted ranges)
    (integer_equations56 tables row inside accepted ranges)
  intro zero
  exact active (Fin.ext zero)

theorem absolute32_air_sound (tables : Tables) (row : Nat)
    (inside : row < (tables 56).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 56 13 row ≠ 0) :
    let v := fun col => (readCell tables 56 col row).val
    pairValue v 2 3 = (if pairValue v 0 1 < 2147483648 then pairValue v 0 1 else 4294967296 - pairValue v 0 1) := by
  exact absolute32_air_sound_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active


theorem absolute64_air_sound_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 55).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 55 27 row ≠ 0) :
    let v := fun col => (readCell tables 55 col row).val
    wordValue v 4 = (if wordValue v 0 < 9223372036854775808 then wordValue v 0 else 18446744073709551616 - wordValue v 0) := by
  apply absolute64_result _ (bounds55 tables row inside accepted ranges)
    (integer_equations55 tables row inside accepted ranges)
  intro zero
  exact active (Fin.ext zero)

theorem absolute64_air_sound (tables : Tables) (row : Nat)
    (inside : row < (tables 55).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 55 27 row ≠ 0) :
    let v := fun col => (readCell tables 55 col row).val
    wordValue v 4 = (if wordValue v 0 < 9223372036854775808 then wordValue v 0 else 18446744073709551616 - wordValue v 0) := by
  exact absolute64_air_sound_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active


end DivRemFV
