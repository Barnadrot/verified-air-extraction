import DivRemFV.UnsignedWitness32
import DivRemFV.SharedTables
import DivRemFV.Generated.Construction
import DivRemFV.Generated.BoundsMap

namespace DivRemFV
open Generated

def unsigned32ZeroTables (a : Nat) : Tables :=
  oneRowTables 63 53 (unsigned32ZeroWitness a)

theorem unsigned32_zero_tables_fixed (a : Nat) : StaticTablesFixed (unsigned32ZeroTables a) := by
  apply oneRowTables_fixed
  intro bits
  simp [rangeTablePairs]

theorem unsigned32_zero_outside (a col : Nat) (outside : 53 ≤ col) :
    unsigned32ZeroWitness a col = 0 := by
  unfold unsigned32ZeroWitness
  split <;> omega

theorem unsigned32_zero_module_complete (a : Nat) (aBound : a < 4294967296) :
    ConstraintsHold (unsigned32ZeroTables a) module63Constraints := by
  apply rows63_complete _ (unsigned32_zero_tables_fixed a)
  · intro row inside
    have zero : row = 0 := by
      simp only [unsigned32ZeroTables, oneRowTables, ↓reduceIte, Array.size_singleton] at inside
      omega
    subst row
    apply bounds63_of_le _ _ (unsigned32_zero_witness_bounds a aBound)
    intro col
    change (readCell (oneRowTables 63 53 (unsigned32ZeroWitness a)) 63 col 0).val ≤ _
    rw [oneRowTables_read_nat _ _ _ _ (unsigned32_zero_outside a)]
    exact Nat.mod_le _ _
  · intro row inside
    have zero : row = 0 := by
      simp only [unsigned32ZeroTables, oneRowTables, ↓reduceIte, Array.size_singleton] at inside
      omega
    subst row
    change Equations63 (fun col => ((readCell (oneRowTables 63 53 (unsigned32ZeroWitness a)) 63 col 0).val : K))
    have equal := funext (oneRowTables_read_field 63 53 · (unsigned32ZeroWitness a) (unsigned32_zero_outside a))
    rw [equal]
    exact unsigned32_zero_witness_field a

theorem unsigned32_zero_slice_complete (a : Nat) (aBound : a < 4294967296) :
    ConstraintsHold (unsigned32ZeroTables a) constraints := by
  apply constraints_from_modules
  · apply rows55_complete _ (unsigned32_zero_tables_fixed a)
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
  · apply rows56_complete _ (unsigned32_zero_tables_fixed a)
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
  · apply rows61_complete _ (unsigned32_zero_tables_fixed a)
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
  · apply rows62_complete _ (unsigned32_zero_tables_fixed a)
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
    · intro message member
      simp [c11984, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c11985, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c11986, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c11989, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c11991, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
  · exact unsigned32_zero_module_complete a aBound
  · apply rows64_complete _ (unsigned32_zero_tables_fixed a)
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
    · intro message member
      simp [c12114, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c12115, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c12116, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c12119, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c12121, Constraint.Holds, messages, Port.messages, unsigned32ZeroTables, oneRowTables, fixedRangeTables] at member
  · apply rows65_complete _ (unsigned32_zero_tables_fixed a)
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
  · apply rows66_complete _ (unsigned32_zero_tables_fixed a)
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32ZeroTables, oneRowTables, fixedRangeTables] at inside

theorem scalarOfNat_encodeLimb (value : Nat) (bounded : value < 65536) :
    scalarOfNat value = encodeLimb value := by
  apply Fin.ext
  simp only [scalarOfNat, encodeLimb, Nat.mod_eq_of_lt bounded,
    Nat.mod_eq_of_lt (lt_trans bounded (by decide : 65536 < fieldModulus))]

theorem unsigned32_zero_columns (a : Nat) (aBound : a < 4294967296) :
    let t := unsigned32ZeroTables a
    (readCell t 63 0 0, readCell t 63 1 0) = encodePair a ∧
    (readCell t 63 2 0, readCell t 63 3 0) = encodePair 0 ∧
    (readCell t 63 4 0, readCell t 63 5 0) = encodePair 4294967295 ∧
    (readCell t 63 6 0, readCell t 63 7 0) = encodePair a := by
  dsimp only [unsigned32ZeroTables]
  rw [oneRowTables_read 63 53 0 _ (by decide), oneRowTables_read 63 53 1 _ (by decide),
    oneRowTables_read 63 53 2 _ (by decide), oneRowTables_read 63 53 3 _ (by decide),
    oneRowTables_read 63 53 4 _ (by decide), oneRowTables_read 63 53 5 _ (by decide),
    oneRowTables_read 63 53 6 _ (by decide), oneRowTables_read 63 53 7 _ (by decide)]
  simp only [unsigned32ZeroWitness]
  have input : (scalarOfNat (a / 65536), scalarOfNat (a % 65536)) = encodePair a := by
    apply Prod.ext
    · exact scalarOfNat_encodeLimb _ (by omega)
    · apply Fin.ext
      change (a % 65536) % fieldModulus = a % 65536
      exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  refine ⟨input, ?_, ?_, input⟩ <;> decide

theorem unsigned32_zero_slice_exists (a : Nat) (aBound : a < 4294967296) :
    ∃ tables : Tables, StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
      0 < (tables 63).size ∧ readCell tables 63 51 0 = 1 ∧
      (readCell tables 63 0 0, readCell tables 63 1 0) = encodePair a ∧
      (readCell tables 63 2 0, readCell tables 63 3 0) = encodePair 0 ∧
      (readCell tables 63 4 0, readCell tables 63 5 0) = encodePair 4294967295 ∧
      (readCell tables 63 6 0, readCell tables 63 7 0) = encodePair a := by
  refine ⟨unsigned32ZeroTables a, unsigned32_zero_tables_fixed a,
    unsigned32_zero_slice_complete a aBound, ?_, ?_, unsigned32_zero_columns a aBound⟩
  · simp [unsigned32ZeroTables, oneRowTables]
  · change readCell (oneRowTables 63 53 (unsigned32ZeroWitness a)) 63 51 0 = 1
    rw [oneRowTables_read _ _ _ _ (by decide)]
    rfl

end DivRemFV

