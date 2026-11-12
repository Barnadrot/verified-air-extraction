import DivRemFV.SignedCalls

namespace DivRemFV
open Generated

theorem signed32_result (v : Nat → Nat) (bounds : Bounds64 v)
    (fieldEquations : Equations64 (fun col => (v col : K)))
    (h : IntegerEquations64 (fun col => (v col : Int)))
    (calls : SignedCalls32 v) (active : v 23 ≠ 0) :
    (pairValue v 4 5, pairValue v 6 7) =
      signedNatResult 32 (pairValue v 0 1) (pairValue v 2 3) := by
  have br := bounds.b23
  have bf := bounds.b22
  have activeOne : v 23 = 1 := by clear * - br active; omega
  have ret : (v 23 : Int) = 1 := by simp [activeOne]
  have cases : v 22 = 0 ∨ v 22 = 1 := by clear * - bf; omega
  rcases cases with zero | one
  · have flag : (v 22 : Int) = 0 := by simp [zero]
    have guard := h.h12081
    have low := h.h12082
    have high := h.h12083
    simp only [ret, flag, one_mul, mul_one, zero_mul, mul_zero, sub_zero, zero_add, add_zero] at guard low high
    have b2 := bounds.b2; have b3 := bounds.b3
    have b4 := bounds.b4; have b5 := bounds.b5
    have denominator : pairValue v 2 3 = 0 := by
      dsimp [pairValue]; clear * - guard b4 b5; omega
    have quotient : pairValue v 4 5 = 4294967295 := by
      dsimp [pairValue]; clear * - guard b4 b5; omega
    have remainder : pairValue v 6 7 = pairValue v 0 1 := by
      dsimp [pairValue]; clear * - low high; omega
    simp only [signedNatResult, denominator, ↓reduceIte, quotient, remainder]
    rfl
  · have flag : (v 22 : Int) = 1 := by simp [one]
    have splitA := h.h12079
    have splitB := h.h12085
    simp only [ret, flag, one_mul, zero_add] at splitA splitB
    have sa := sign_from_digits (v 0) (v 1) 65536 (v 18) (v 12)
      bounds.b1 bounds.b18 bounds.b12 splitA
    have sb := sign_from_digits (v 2) (v 3) 65536 (v 20) (v 17)
      bounds.b3 bounds.b20 bounds.b17 splitB
    have signA : v 12 = signValue 32 (pairValue v 0 1) := by
      simpa [signValue, pairValue] using sa
    have signB : v 17 = signValue 32 (pairValue v 2 3) := by
      simpa [signValue, pairValue] using sb
    have nonzero : pairValue v 2 3 ≠ 0 := by
      intro zero
      have zeros : v 2 = 0 ∧ v 3 = 0 := by
        dsimp [pairValue] at zero; omega
      have check := fieldEquations.h12080
      norm_num [activeOne, one, zeros.1, zeros.2] at check
    have bounded : pairValue v 2 3 < 2 ^ 32 := by
      have b2 := bounds.b2; have b3 := bounds.b3
      dsimp [pairValue]; clear * - b2 b3; omega
    have magnitudeNonzero := Nat.ne_of_gt (magnitude_positive 32 _
      (Nat.pos_of_ne_zero nonzero) bounded)
    have unsignedQ := calls.quotient
    have unsignedR := calls.remainder
    rw [calls.absoluteA, calls.absoluteB, if_neg magnitudeNonzero] at unsignedQ unsignedR
    unfold signedNatResult
    rw [if_neg nonzero]
    apply Prod.ext
    · change pairValue v 4 5 =
        if signValue 32 (pairValue v 0 1) = signValue 32 (pairValue v 2 3)
        then _ else _
      by_cases same : v 12 = v 17
      · have equalSigns : signValue 32 (pairValue v 0 1) = signValue 32 (pairValue v 2 3) := by
          rw [← signA, ← signB]; exact same
        rw [if_pos equalSigns]
        have low := h.h12086
        have high := h.h12087
        simp only [ret, flag, same, sub_self, one_mul, mul_one, zero_mul, sub_zero] at low high
        have equal : pairValue v 4 5 = pairValue v 8 9 := by
          dsimp [pairValue]; clear * - low high; omega
        exact equal.trans unsignedQ
      · have differentSigns : signValue 32 (pairValue v 0 1) ≠ signValue 32 (pairValue v 2 3) := by
          rw [← signA, ← signB]; exact same
        rw [if_neg differentSigns]
        have selected : v 24 ≠ 0 := by
          intro zero
          have check := h.h12117
          simp only [ret, flag, zero, Nat.cast_zero, one_mul, mul_one, sub_zero] at check
          apply same
          clear * - check; omega
        rw [calls.negativeQ selected, unsignedQ]
    · change pairValue v 6 7 = if signValue 32 (pairValue v 0 1) = 0 then _ else _
      by_cases positive : v 12 = 0
      · have nonnegative : signValue 32 (pairValue v 0 1) = 0 := signA.symm.trans positive
        rw [if_pos nonnegative]
        have low := h.h12088
        have high := h.h12089
        simp only [ret, flag, positive, Nat.cast_zero, one_mul, mul_one, sub_zero] at low high
        have equal : pairValue v 6 7 = pairValue v 10 11 := by
          dsimp [pairValue]; clear * - low high; omega
        exact equal.trans unsignedR
      · have negative : signValue 32 (pairValue v 0 1) ≠ 0 := by rw [← signA]; exact positive
        rw [if_neg negative]
        have signOne : v 12 = 1 := by have b12 := bounds.b12; clear * - b12 positive; omega
        have selected : v 25 ≠ 0 := by
          intro zero
          have check := fieldEquations.h12120
          norm_num [activeOne, one, signOne, zero] at check
        rw [calls.negativeR selected, unsignedR]

theorem signed32_air_sound_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 64).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 64 23 row ≠ 0) :
    let v := fun col => (readCell tables 64 col row).val
    (pairValue v 4 5, pairValue v 6 7) =
      signedNatResult 32 (pairValue v 0 1) (pairValue v 2 3) := by
  apply signed32_result _ (bounds64 tables row inside accepted ranges)
    (equations64 tables row inside accepted) (integer_equations64 tables row inside accepted ranges)
    (signed_calls32_of_ranges tables row inside accepted ranges active)
  intro zero
  exact active (Fin.ext zero)

theorem signed32_air_sound (tables : Tables) (row : Nat)
    (inside : row < (tables 64).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 64 23 row ≠ 0) :
    let v := fun col => (readCell tables 64 col row).val
    (pairValue v 4 5, pairValue v 6 7) =
      signedNatResult 32 (pairValue v 0 1) (pairValue v 2 3) := by
  exact signed32_air_sound_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active


theorem signed64_result (v : Nat → Nat) (bounds : Bounds62 v)
    (fieldEquations : Equations62 (fun col => (v col : K)))
    (h : IntegerEquations62 (fun col => (v col : Int)))
    (calls : SignedCalls64 v) (active : v 43 ≠ 0) :
    (wordValue v 8, wordValue v 12) =
      signedNatResult 64 (wordValue v 0) (wordValue v 4) := by
  have br := bounds.b43
  have bf := bounds.b42
  have activeOne : v 43 = 1 := by clear * - br active; omega
  have ret : (v 43 : Int) = 1 := by simp [activeOne]
  have cases : v 42 = 0 ∨ v 42 = 1 := by clear * - bf; omega
  rcases cases with zero | one
  · have flag : (v 42 : Int) = 0 := by simp [zero]
    have guard := h.h11923
    have low := h.h11924
    have middle0 := h.h11925
    have middle1 := h.h11926
    have high := h.h11927
    simp only [ret, flag, one_mul, mul_one, zero_mul, mul_zero, sub_zero, zero_add, add_zero] at guard low middle0 middle1 high
    have b2 := bounds.b4; have b3 := bounds.b7
    have b4 := bounds.b8; have b5 := bounds.b9
    have b6 := bounds.b10; have b7 := bounds.b11
    have denominator : wordValue v 4 = 0 := by
      dsimp [wordValue]; clear * - guard b4 b5 b6 b7; omega
    have quotient : wordValue v 8 = 18446744073709551615 := by
      dsimp [wordValue]; clear * - guard b4 b5 b6 b7; omega
    have remainder : wordValue v 12 = wordValue v 0 := by
      dsimp [wordValue]; clear * - low middle0 middle1 high; omega
    simp only [signedNatResult, denominator, ↓reduceIte, quotient, remainder]
    rfl
  · have flag : (v 42 : Int) = 1 := by simp [one]
    have splitA := h.h11921
    have splitB := h.h11931
    simp only [ret, flag, one_mul, zero_add] at splitA splitB
    have aRest : 4294967296 * v 1 + 65536 * v 2 + v 3 < 281474976710656 := by
      have b1 := bounds.b1; have b2 := bounds.b2; have b3 := bounds.b3
      clear * - b1 b2 b3; omega
    have bRest : 4294967296 * v 5 + 65536 * v 6 + v 7 < 281474976710656 := by
      have b5 := bounds.b5; have b6 := bounds.b6; have b7 := bounds.b7
      clear * - b5 b6 b7; omega
    have sa := sign_from_digits (v 0) (4294967296 * v 1 + 65536 * v 2 + v 3) 281474976710656 (v 34) (v 24)
      aRest bounds.b34 bounds.b24 splitA
    have sb := sign_from_digits (v 4) (4294967296 * v 5 + 65536 * v 6 + v 7) 281474976710656 (v 38) (v 33)
      bRest bounds.b38 bounds.b33 splitB
    have signA : v 24 = signValue 64 (wordValue v 0) := by
      simpa [signValue, wordValue, Nat.add_assoc] using sa
    have signB : v 33 = signValue 64 (wordValue v 4) := by
      simpa [signValue, wordValue, Nat.add_assoc] using sb
    have nonzero : wordValue v 4 ≠ 0 := by
      intro zero
      have zeros : v 4 = 0 ∧ v 5 = 0 ∧ v 6 = 0 ∧ v 7 = 0 := by
        dsimp [wordValue] at zero; omega
      have check := fieldEquations.h11922
      norm_num [activeOne, one, zeros.1, zeros.2.1, zeros.2.2.1, zeros.2.2.2] at check
    have bounded : wordValue v 4 < 2 ^ 64 := by
      have b2 := bounds.b4; have b3 := bounds.b5
      have b4 := bounds.b6; have b5 := bounds.b7
      dsimp [wordValue]; clear * - b2 b3 b4 b5; omega
    have magnitudeNonzero := Nat.ne_of_gt (magnitude_positive 64 _
      (Nat.pos_of_ne_zero nonzero) bounded)
    have unsignedQ := calls.quotient
    have unsignedR := calls.remainder
    rw [calls.absoluteA, calls.absoluteB, if_neg magnitudeNonzero] at unsignedQ unsignedR
    unfold signedNatResult
    rw [if_neg nonzero]
    apply Prod.ext
    · change wordValue v 8 =
        if signValue 64 (wordValue v 0) = signValue 64 (wordValue v 4)
        then _ else _
      by_cases same : v 24 = v 33
      · have equalSigns : signValue 64 (wordValue v 0) = signValue 64 (wordValue v 4) := by
          rw [← signA, ← signB]; exact same
        rw [if_pos equalSigns]
        have low := h.h11932
        have middle0 := h.h11933
        have middle1 := h.h11934
        have high := h.h11935
        simp only [ret, flag, same, sub_self, one_mul, mul_one, zero_mul, sub_zero] at low middle0 middle1 high
        have equal : wordValue v 8 = wordValue v 16 := by
          dsimp [wordValue]; clear * - low middle0 middle1 high; omega
        exact equal.trans unsignedQ
      · have differentSigns : signValue 64 (wordValue v 0) ≠ signValue 64 (wordValue v 4) := by
          rw [← signA, ← signB]; exact same
        rw [if_neg differentSigns]
        have selected : v 44 ≠ 0 := by
          intro zero
          have check := h.h11987
          simp only [ret, flag, zero, Nat.cast_zero, one_mul, mul_one, sub_zero] at check
          apply same
          clear * - check; omega
        rw [calls.negativeQ selected, unsignedQ]
    · change wordValue v 12 = if signValue 64 (wordValue v 0) = 0 then _ else _
      by_cases positive : v 24 = 0
      · have nonnegative : signValue 64 (wordValue v 0) = 0 := signA.symm.trans positive
        rw [if_pos nonnegative]
        have low := h.h11936
        have middle0 := h.h11937
        have middle1 := h.h11938
        have high := h.h11939
        simp only [ret, flag, positive, Nat.cast_zero, one_mul, mul_one, sub_zero] at low middle0 middle1 high
        have equal : wordValue v 12 = wordValue v 20 := by
          dsimp [wordValue]; clear * - low middle0 middle1 high; omega
        exact equal.trans unsignedR
      · have negative : signValue 64 (wordValue v 0) ≠ 0 := by rw [← signA]; exact positive
        rw [if_neg negative]
        have signOne : v 24 = 1 := by have b12 := bounds.b24; clear * - b12 positive; omega
        have selected : v 45 ≠ 0 := by
          intro zero
          have check := fieldEquations.h11990
          norm_num [activeOne, one, signOne, zero] at check
        rw [calls.negativeR selected, unsignedR]

theorem signed64_air_sound_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 62 43 row ≠ 0) :
    let v := fun col => (readCell tables 62 col row).val
    (wordValue v 8, wordValue v 12) =
      signedNatResult 64 (wordValue v 0) (wordValue v 4) := by
  apply signed64_result _ (bounds62 tables row inside accepted ranges)
    (equations62 tables row inside accepted) (integer_equations62 tables row inside accepted ranges)
    (signed_calls64_of_ranges tables row inside accepted ranges active)
  intro zero
  exact active (Fin.ext zero)

theorem signed64_air_sound (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 62 43 row ≠ 0) :
    let v := fun col => (readCell tables 62 col row).val
    (wordValue v 8, wordValue v 12) =
      signedNatResult 64 (wordValue v 0) (wordValue v 4) := by
  exact signed64_air_sound_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active


end DivRemFV

