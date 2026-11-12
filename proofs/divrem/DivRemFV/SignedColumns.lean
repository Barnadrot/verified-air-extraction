import DivRemFV.SignedRows

namespace DivRemFV
open Generated

theorem signed32_air_columns_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 64).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 64 23 row ≠ 0)
    (a b : BitVec 32) (inputA : pairValue (fun col => (readCell tables 64 col row).val) 0 1 = a.toNat)
    (inputB : pairValue (fun col => (readCell tables 64 col row).val) 2 3 = b.toNat) :
    (readCell tables 64 4 row, readCell tables 64 5 row) = encodePair (signedQuotient a b).toNat ∧
    (readCell tables 64 6 row, readCell tables 64 7 row) = encodePair (signedRemainder a b).toNat := by
  have bounds := bounds64 tables row inside accepted ranges
  have result := signed32_air_sound_of_ranges tables row inside accepted ranges active
  change (pairValue (fun col => (readCell tables 64 col row).val) 4 5, pairValue (fun col => (readCell tables 64 col row).val) 6 7) = _ at result
  rw [inputA, inputB, signedNat_toNat, magnitudeAlgorithm_arch32] at result
  have quotient := congrArg Prod.fst result
  have remainder := congrArg Prod.snd result
  simp only [Prod.fst, Prod.snd] at quotient remainder
  have q := pair_limbs (readCell tables 64 4 row) (readCell tables 64 5 row)
    bounds.b4 bounds.b5
  change _ = encodePair (pairValue (fun col => (readCell tables 64 col row).val) 4 5) at q
  rw [quotient] at q
  have r := pair_limbs (readCell tables 64 6 row) (readCell tables 64 7 row)
    bounds.b6 bounds.b7
  change _ = encodePair (pairValue (fun col => (readCell tables 64 col row).val) 6 7) at r
  rw [remainder] at r
  exact ⟨q,r⟩

theorem signed32_air_columns (tables : Tables) (row : Nat)
    (inside : row < (tables 64).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 64 23 row ≠ 0)
    (a b : BitVec 32) (inputA : pairValue (fun col => (readCell tables 64 col row).val) 0 1 = a.toNat)
    (inputB : pairValue (fun col => (readCell tables 64 col row).val) 2 3 = b.toNat) :
    (readCell tables 64 4 row, readCell tables 64 5 row) = encodePair (signedQuotient a b).toNat ∧
    (readCell tables 64 6 row, readCell tables 64 7 row) = encodePair (signedRemainder a b).toNat := by
  exact signed32_air_columns_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active a b inputA inputB


theorem signed64_air_columns_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 62 43 row ≠ 0)
    (a b : BitVec 64) (inputA : wordValue (fun col => (readCell tables 62 col row).val) 0 = a.toNat)
    (inputB : wordValue (fun col => (readCell tables 62 col row).val) 4 = b.toNat) :
    (readCell tables 62 8 row, readCell tables 62 9 row, readCell tables 62 10 row, readCell tables 62 11 row) = encodeFour (signedQuotient a b).toNat ∧
    (readCell tables 62 12 row, readCell tables 62 13 row, readCell tables 62 14 row, readCell tables 62 15 row) = encodeFour (signedRemainder a b).toNat := by
  have bounds := bounds62 tables row inside accepted ranges
  have result := signed64_air_sound_of_ranges tables row inside accepted ranges active
  change (wordValue (fun col => (readCell tables 62 col row).val) 8, wordValue (fun col => (readCell tables 62 col row).val) 12) = _ at result
  rw [inputA, inputB, signedNat_toNat, magnitudeAlgorithm_arch64] at result
  have quotient := congrArg Prod.fst result
  have remainder := congrArg Prod.snd result
  simp only [Prod.fst, Prod.snd] at quotient remainder
  have q := four_limbs (readCell tables 62 8 row) (readCell tables 62 9 row) (readCell tables 62 10 row) (readCell tables 62 11 row)
    bounds.b8 bounds.b9 bounds.b10 bounds.b11
  change _ = encodeFour (wordValue (fun col => (readCell tables 62 col row).val) 8) at q
  rw [quotient] at q
  have r := four_limbs (readCell tables 62 12 row) (readCell tables 62 13 row) (readCell tables 62 14 row) (readCell tables 62 15 row)
    bounds.b12 bounds.b13 bounds.b14 bounds.b15
  change _ = encodeFour (wordValue (fun col => (readCell tables 62 col row).val) 12) at r
  rw [remainder] at r
  exact ⟨q,r⟩

theorem signed64_air_columns (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 62 43 row ≠ 0)
    (a b : BitVec 64) (inputA : wordValue (fun col => (readCell tables 62 col row).val) 0 = a.toNat)
    (inputB : wordValue (fun col => (readCell tables 62 col row).val) 4 = b.toNat) :
    (readCell tables 62 8 row, readCell tables 62 9 row, readCell tables 62 10 row, readCell tables 62 11 row) = encodeFour (signedQuotient a b).toNat ∧
    (readCell tables 62 12 row, readCell tables 62 13 row, readCell tables 62 14 row, readCell tables 62 15 row) = encodeFour (signedRemainder a b).toNat := by
  exact signed64_air_columns_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active a b inputA inputB


end DivRemFV

