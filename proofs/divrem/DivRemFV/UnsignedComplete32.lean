import DivRemFV.UnsignedNonzero32
import DivRemFV.UnsignedZero32

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def unsigned32NonzeroTables (a b q r w : Nat) : Tables :=
  oneRowTables 63 53 (unsigned32NonzeroWitness a b q r w)

theorem unsigned32_nonzero_tables_fixed (a b q r w : Nat) :
    StaticTablesFixed (unsigned32NonzeroTables a b q r w) := by
  apply oneRowTables_fixed
  intro bits
  simp [rangeTablePairs]

theorem unsigned32_nonzero_outside (a b q r w col : Nat) (outside : 53 ≤ col) :
    unsigned32NonzeroWitness a b q r w col = 0 := by
  unfold unsigned32NonzeroWitness
  split <;> omega

theorem unsigned32_nonzero_module_complete (a b q r w : Nat)
    (aBound : a < 4294967296) (bBound : b < 4294967296)
    (qBound : q < 4294967296) (rBound : r < 4294967296) (wBound : w < 4294967296)
    (identity : a = q * b + r) (remainderBound : b = r + w + 1) :
    ConstraintsHold (unsigned32NonzeroTables a b q r w) module63Constraints := by
  apply rows63_complete _ (unsigned32_nonzero_tables_fixed a b q r w)
  · intro row inside
    have zero : row = 0 := by
      simp only [unsigned32NonzeroTables, oneRowTables, ↓reduceIte, Array.size_singleton] at inside
      omega
    subst row
    apply bounds63_of_le _ _ (unsigned32_nonzero_witness_bounds a b q r w
      aBound bBound qBound rBound wBound identity)
    intro col
    change (readCell (oneRowTables 63 53 (unsigned32NonzeroWitness a b q r w)) 63 col 0).val ≤ _
    rw [oneRowTables_read_nat _ _ _ _ (unsigned32_nonzero_outside a b q r w)]
    exact Nat.mod_le _ _
  · intro row inside
    have zero : row = 0 := by
      simp only [unsigned32NonzeroTables, oneRowTables, ↓reduceIte, Array.size_singleton] at inside
      omega
    subst row
    change Equations63 (fun col => ((readCell (oneRowTables 63 53 (unsigned32NonzeroWitness a b q r w)) 63 col 0).val : K))
    have equal := funext (oneRowTables_read_field 63 53 · (unsigned32NonzeroWitness a b q r w)
      (unsigned32_nonzero_outside a b q r w))
    rw [equal]
    exact unsigned32_nonzero_witness_field a b q r w aBound bBound qBound rBound wBound identity remainderBound

theorem unsigned32_nonzero_slice_complete (a b q r w : Nat)
    (aBound : a < 4294967296) (bBound : b < 4294967296)
    (qBound : q < 4294967296) (rBound : r < 4294967296) (wBound : w < 4294967296)
    (identity : a = q * b + r) (remainderBound : b = r + w + 1) :
    ConstraintsHold (unsigned32NonzeroTables a b q r w) constraints := by
  apply constraints_from_modules
  · apply rows55_complete _ (unsigned32_nonzero_tables_fixed a b q r w)
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
  · apply rows56_complete _ (unsigned32_nonzero_tables_fixed a b q r w)
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
  · apply rows61_complete _ (unsigned32_nonzero_tables_fixed a b q r w)
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
  · apply rows62_complete _ (unsigned32_nonzero_tables_fixed a b q r w)
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
    · intro message member
      simp [c11984, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c11985, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c11986, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c11989, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c11991, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
  · exact unsigned32_nonzero_module_complete a b q r w aBound bBound qBound rBound wBound identity remainderBound
  · apply rows64_complete _ (unsigned32_nonzero_tables_fixed a b q r w)
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
    · intro message member
      simp [c12114, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c12115, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c12116, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c12119, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
    · intro message member
      simp [c12121, Constraint.Holds, messages, Port.messages, unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at member
  · apply rows65_complete _ (unsigned32_nonzero_tables_fixed a b q r w)
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
  · apply rows66_complete _ (unsigned32_nonzero_tables_fixed a b q r w)
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside
    · intro row inside
      simp [unsigned32NonzeroTables, oneRowTables, fixedRangeTables] at inside

theorem scalarPairOfNat (value : Nat) (bounded : value < 4294967296) :
    (scalarOfNat (value / 65536), scalarOfNat (value % 65536)) = encodePair value := by
  apply Prod.ext
  · exact scalarOfNat_encodeLimb _ (by omega)
  · apply Fin.ext
    change (value % 65536) % fieldModulus = value % 65536
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem unsigned32_nonzero_columns (a b q r w : Nat)
    (aBound : a < 4294967296) (bBound : b < 4294967296)
    (qBound : q < 4294967296) (rBound : r < 4294967296) :
    let t := unsigned32NonzeroTables a b q r w
    (readCell t 63 0 0, readCell t 63 1 0) = encodePair a ∧
    (readCell t 63 2 0, readCell t 63 3 0) = encodePair b ∧
    (readCell t 63 4 0, readCell t 63 5 0) = encodePair q ∧
    (readCell t 63 6 0, readCell t 63 7 0) = encodePair r := by
  dsimp only [unsigned32NonzeroTables]
  rw [oneRowTables_read 63 53 0 _ (by decide), oneRowTables_read 63 53 1 _ (by decide),
    oneRowTables_read 63 53 2 _ (by decide), oneRowTables_read 63 53 3 _ (by decide),
    oneRowTables_read 63 53 4 _ (by decide), oneRowTables_read 63 53 5 _ (by decide),
    oneRowTables_read 63 53 6 _ (by decide), oneRowTables_read 63 53 7 _ (by decide)]
  exact ⟨scalarPairOfNat a aBound, scalarPairOfNat b bBound, scalarPairOfNat q qBound, scalarPairOfNat r rBound⟩

theorem unsigned32_nonzero_slice_exists (a b : Nat) (aBound : a < 4294967296)
    (bBound : b < 4294967296) (nonzero : b ≠ 0) :
    ∃ tables : Tables, StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
      0 < (tables 63).size ∧ readCell tables 63 51 0 = 1 ∧
      (readCell tables 63 0 0, readCell tables 63 1 0) = encodePair a ∧
      (readCell tables 63 2 0, readCell tables 63 3 0) = encodePair b ∧
      (readCell tables 63 4 0, readCell tables 63 5 0) = encodePair (a / b) ∧
      (readCell tables 63 6 0, readCell tables 63 7 0) = encodePair (a % b) := by
  let q := a / b
  let r := a % b
  let w := b - r - 1
  have qBound : q < 4294967296 := lt_of_le_of_lt (Nat.div_le_self _ _) aBound
  have remainderSmall : r < b := Nat.mod_lt _ (Nat.pos_of_ne_zero nonzero)
  have rBound : r < 4294967296 := lt_trans remainderSmall bBound
  have wBound : w < 4294967296 := by dsimp [w]; omega
  have identity : a = q * b + r := by
    simpa only [q, r, Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div a b).symm
  have remainderBound : b = r + w + 1 := by dsimp [w]; omega
  refine ⟨unsigned32NonzeroTables a b q r w, unsigned32_nonzero_tables_fixed a b q r w,
    unsigned32_nonzero_slice_complete a b q r w aBound bBound qBound rBound wBound identity remainderBound,
    ?_, ?_, unsigned32_nonzero_columns a b q r w aBound bBound qBound rBound⟩
  · simp [unsigned32NonzeroTables, oneRowTables]
  · change readCell (oneRowTables 63 53 (unsigned32NonzeroWitness a b q r w)) 63 51 0 = 1
    rw [oneRowTables_read _ _ _ _ (by decide)]
    rfl

end DivRemFV

