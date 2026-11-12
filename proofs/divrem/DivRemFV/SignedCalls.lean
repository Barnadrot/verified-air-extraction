import DivRemFV.Generated.Calls
import DivRemFV.AbsoluteValue
import DivRemFV.Negation
import DivRemFV.SignedSpec

namespace DivRemFV
open Generated

structure SignedCalls32 (v : Nat → Nat) : Prop where
  absoluteA : pairValue v 13 14 = magnitudeNat 32 (pairValue v 0 1)
  absoluteB : pairValue v 15 16 = magnitudeNat 32 (pairValue v 2 3)
  quotient : pairValue v 8 9 = (if pairValue v 15 16 = 0 then 4294967295 else pairValue v 13 14 / pairValue v 15 16)
  remainder : pairValue v 10 11 = (if pairValue v 15 16 = 0 then pairValue v 13 14 else pairValue v 13 14 % pairValue v 15 16)
  negativeQ : v 24 ≠ 0 → pairValue v 4 5 = negateNat 32 (pairValue v 8 9)
  negativeR : v 25 ≠ 0 → pairValue v 6 7 = negateNat 32 (pairValue v 10 11)

theorem signed_calls32_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 64).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 64 23 row ≠ 0) :
    SignedCalls32 (fun col => (readCell tables 64 col row).val) := by
  constructor
  · obtain ⟨callee, inCallee, selected, h0,h1,h2,h3⟩ := call12114 tables row inside accepted active
    have result := absolute32_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa only [magnitudeNat, pairValue, wordValue, h0, h1, h2, h3] using result
  · obtain ⟨callee, inCallee, selected, h0,h1,h2,h3⟩ := call12115 tables row inside accepted active
    have result := absolute32_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa only [magnitudeNat, pairValue, wordValue, h0, h1, h2, h3] using result
  · obtain ⟨callee, inCallee, selected, h0,h1,h2,h3,h4,h5,h6,h7⟩ := call12116 tables row inside accepted active
    have result := unsigned32_air_sound tables callee inCallee accepted ranges selected
    simpa only [magnitudeNat, pairValue, wordValue, h0, h1, h2, h3, h4, h5, h6, h7] using result.1
  · obtain ⟨callee, inCallee, selected, h0,h1,h2,h3,h4,h5,h6,h7⟩ := call12116 tables row inside accepted active
    have result := unsigned32_air_sound tables callee inCallee accepted ranges selected
    simpa only [magnitudeNat, pairValue, wordValue, h0, h1, h2, h3, h4, h5, h6, h7] using result.2
  · intro enabled
    have sourceActive : readCell tables 64 24 row ≠ 0 := by
      intro zero
      exact enabled (congrArg Fin.val zero)
    obtain ⟨callee, inCallee, selected, h0,h1,h2,h3⟩ := call12119 tables row inside accepted sourceActive
    have result := negative32_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa [negateNat, pairValue, wordValue, h0, h1, h2, h3] using result
  · intro enabled
    have sourceActive : readCell tables 64 25 row ≠ 0 := by
      intro zero
      exact enabled (congrArg Fin.val zero)
    obtain ⟨callee, inCallee, selected, h0,h1,h2,h3⟩ := call12121 tables row inside accepted sourceActive
    have result := negative32_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa [negateNat, pairValue, wordValue, h0, h1, h2, h3] using result

theorem signed_calls32 (tables : Tables) (row : Nat)
    (inside : row < (tables 64).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 64 23 row ≠ 0) :
    SignedCalls32 (fun col => (readCell tables 64 col row).val) := by
  exact signed_calls32_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active

structure SignedCalls64 (v : Nat → Nat) : Prop where
  absoluteA : wordValue v 25 = magnitudeNat 64 (wordValue v 0)
  absoluteB : wordValue v 29 = magnitudeNat 64 (wordValue v 4)
  quotient : wordValue v 16 = (if wordValue v 29 = 0 then 18446744073709551615 else wordValue v 25 / wordValue v 29)
  remainder : wordValue v 20 = (if wordValue v 29 = 0 then wordValue v 25 else wordValue v 25 % wordValue v 29)
  negativeQ : v 44 ≠ 0 → wordValue v 8 = negateNat 64 (wordValue v 16)
  negativeR : v 45 ≠ 0 → wordValue v 12 = negateNat 64 (wordValue v 20)

theorem signed_calls64_of_ranges (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 62 43 row ≠ 0) :
    SignedCalls64 (fun col => (readCell tables 62 col row).val) := by
  constructor
  · obtain ⟨callee, inCallee, selected, h0,h1,h2,h3,h4,h5,h6,h7⟩ := call11984 tables row inside accepted active
    have result := absolute64_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa only [magnitudeNat, pairValue, wordValue, h0, h1, h2, h3, h4, h5, h6, h7] using result
  · obtain ⟨callee, inCallee, selected, h0,h1,h2,h3,h4,h5,h6,h7⟩ := call11985 tables row inside accepted active
    have result := absolute64_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa only [magnitudeNat, pairValue, wordValue, h0, h1, h2, h3, h4, h5, h6, h7] using result
  · obtain ⟨callee, inCallee, selected, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := call11986 tables row inside accepted active
    have result := unsigned64_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa only [magnitudeNat, pairValue, wordValue, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] using result.1
  · obtain ⟨callee, inCallee, selected, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := call11986 tables row inside accepted active
    have result := unsigned64_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa only [magnitudeNat, pairValue, wordValue, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] using result.2
  · intro enabled
    have sourceActive : readCell tables 62 44 row ≠ 0 := by
      intro zero
      exact enabled (congrArg Fin.val zero)
    obtain ⟨callee, inCallee, selected, h0,h1,h2,h3,h4,h5,h6,h7⟩ := call11989 tables row inside accepted sourceActive
    have result := negative64_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa [negateNat, pairValue, wordValue, h0, h1, h2, h3, h4, h5, h6, h7] using result
  · intro enabled
    have sourceActive : readCell tables 62 45 row ≠ 0 := by
      intro zero
      exact enabled (congrArg Fin.val zero)
    obtain ⟨callee, inCallee, selected, h0,h1,h2,h3,h4,h5,h6,h7⟩ := call11991 tables row inside accepted sourceActive
    have result := negative64_air_sound_of_ranges tables callee inCallee accepted ranges selected
    simpa [negateNat, pairValue, wordValue, h0, h1, h2, h3, h4, h5, h6, h7] using result

theorem signed_calls64 (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 62 43 row ≠ 0) :
    SignedCalls64 (fun col => (readCell tables 62 col row).val) := by
  exact signed_calls64_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active

end DivRemFV
