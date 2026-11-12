import DivRemFV.UnsignedNonzero64
import DivRemFV.Unsigned64Result
import DivRemFV.UnsignedZero32

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def readFour (tables : Tables) (mid start : Nat) (row : Int) : Scalar × Scalar × Scalar × Scalar :=
  (readCell tables mid start row,readCell tables mid (start+1) row,
    readCell tables mid (start+2) row,readCell tables mid (start+3) row)

theorem readFour_one_row (mid width start : Nat) (values : Nat → Nat) (inside : start + 3 < width) :
    readFour (oneRowTables mid width values) mid start 0 =
      (scalarOfNat (values start),scalarOfNat (values (start+1)),
        scalarOfNat (values (start+2)),scalarOfNat (values (start+3))) := by
  unfold readFour
  rw [oneRowTables_read _ _ _ _ (by omega),oneRowTables_read _ _ _ _ (by omega),
    oneRowTables_read _ _ _ _ (by omega),oneRowTables_read _ _ _ _ (by omega)]

theorem unsigned64_tables_fixed (values : Nat → Nat) :
    StaticTablesFixed (oneRowTables 61 123 values) := by
  apply oneRowTables_fixed
  intro bits
  simp [rangeTablePairs]

theorem unsigned64_one_row_module_complete (values : Nat → Nat)
    (outside : ∀ col,123 ≤ col → values col = 0)
    (bounds : Bounds61 values) (equations : Equations61 (fun col => (values col : K))) :
    ConstraintsHold (oneRowTables 61 123 values) module61Constraints := by
  apply rows61_complete _ (unsigned64_tables_fixed values)
  · intro row inside
    have zero : row = 0 := by simp only [oneRowTables,↓reduceIte,Array.size_singleton] at inside; omega
    subst row
    apply bounds61_of_le _ _ bounds
    intro col
    change (readCell (oneRowTables 61 123 values) 61 col 0).val ≤ _
    rw [oneRowTables_read_nat _ _ _ _ outside]
    exact Nat.mod_le _ _
  · intro row inside
    have zero : row = 0 := by simp only [oneRowTables,↓reduceIte,Array.size_singleton] at inside; omega
    subst row
    change Equations61 (fun col => ((readCell (oneRowTables 61 123 values) 61 col 0).val : K))
    have equal := funext (oneRowTables_read_field 61 123 · values outside)
    rw [equal]
    exact equations

theorem unsigned64_one_row_slice_complete (values : Nat → Nat)
    (outside : ∀ col,123 ≤ col → values col = 0)
    (bounds : Bounds61 values) (equations : Equations61 (fun col => (values col : K))) :
    ConstraintsHold (oneRowTables 61 123 values) constraints := by
  apply constraints_from_modules
  · apply rows55_complete _ (unsigned64_tables_fixed values)
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
  · apply rows56_complete _ (unsigned64_tables_fixed values)
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
  · exact unsigned64_one_row_module_complete values outside bounds equations
  · apply rows62_complete _ (unsigned64_tables_fixed values)
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
    · intro message member
      simp [c11984,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
    · intro message member
      simp [c11985,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
    · intro message member
      simp [c11986,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
    · intro message member
      simp [c11989,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
    · intro message member
      simp [c11991,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
  · apply rows63_complete _ (unsigned64_tables_fixed values)
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
  · apply rows64_complete _ (unsigned64_tables_fixed values)
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
    · intro message member
      simp [c12114,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
    · intro message member
      simp [c12115,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
    · intro message member
      simp [c12116,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
    · intro message member
      simp [c12119,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
    · intro message member
      simp [c12121,Constraint.Holds,messages,Port.messages,oneRowTables,fixedRangeTables] at member
  · apply rows65_complete _ (unsigned64_tables_fixed values)
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
  · apply rows66_complete _ (unsigned64_tables_fixed values)
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside
    · intro row inside
      simp [oneRowTables,fixedRangeTables] at inside

theorem scalarFourOfNat (value : Nat) (bounded : value < 18446744073709551616) :
    (scalarOfNat (value / 281474976710656),scalarOfNat (value / 4294967296 % 65536),
      scalarOfNat (value / 65536 % 65536),scalarOfNat (value % 65536)) = encodeFour value := by
  apply Prod.ext
  · exact scalarOfNat_encodeLimb _ (by omega)
  · apply Prod.ext
    · apply Fin.ext
      change (value / 4294967296 % 65536) % fieldModulus = value / 4294967296 % 65536
      exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))
    · apply Prod.ext
      · apply Fin.ext
        change (value / 65536 % 65536) % fieldModulus = value / 65536 % 65536
        exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))
      · apply Fin.ext
        change (value % 65536) % fieldModulus = value % 65536
        exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem unsigned64_nonzero_outside (a b q r w col : Nat) (outside : 123 ≤ col) :
    unsigned64NonzeroWitness a b q r w col = 0 := by
  unfold unsigned64NonzeroWitness
  split <;> omega

theorem unsigned64_zero_outside (a col : Nat) (outside : 123 ≤ col) :
    unsigned64ZeroWitness a col = 0 := by
  unfold unsigned64ZeroWitness
  split <;> omega

theorem unsigned64_nonzero_columns (a b q r w : Nat)
    (aBound : a < 18446744073709551616) (bBound : b < 18446744073709551616)
    (qBound : q < 18446744073709551616) (rBound : r < 18446744073709551616) :
    let t := oneRowTables 61 123 (unsigned64NonzeroWitness a b q r w)
    readFour t 61 0 0 = encodeFour a ∧ readFour t 61 4 0 = encodeFour b ∧
    readFour t 61 8 0 = encodeFour q ∧ readFour t 61 12 0 = encodeFour r := by
  dsimp only
  rw [readFour_one_row 61 123 0 _ (by decide),readFour_one_row 61 123 4 _ (by decide),
    readFour_one_row 61 123 8 _ (by decide),readFour_one_row 61 123 12 _ (by decide)]
  exact ⟨scalarFourOfNat a aBound,scalarFourOfNat b bBound,scalarFourOfNat q qBound,scalarFourOfNat r rBound⟩

theorem unsigned64_zero_columns (a : Nat) (aBound : a < 18446744073709551616) :
    let t := oneRowTables 61 123 (unsigned64ZeroWitness a)
    readFour t 61 0 0 = encodeFour a ∧ readFour t 61 4 0 = encodeFour 0 ∧
    readFour t 61 8 0 = encodeFour 18446744073709551615 ∧ readFour t 61 12 0 = encodeFour a := by
  dsimp only
  rw [readFour_one_row 61 123 0 _ (by decide),readFour_one_row 61 123 4 _ (by decide),
    readFour_one_row 61 123 8 _ (by decide),readFour_one_row 61 123 12 _ (by decide)]
  refine ⟨scalarFourOfNat a aBound,?_,?_,scalarFourOfNat a aBound⟩ <;>
    norm_num [unsigned64ZeroWitness,scalarOfNat,encodeFour,encodeLimb,fieldModulus]

theorem unsigned64_slice_exists (a b : Nat) (aBound : a < 18446744073709551616)
    (bBound : b < 18446744073709551616) :
    ∃ tables : Tables,StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
      0 < (tables 61).size ∧ readCell tables 61 121 0 = 1 ∧
      readFour tables 61 0 0 = encodeFour a ∧ readFour tables 61 4 0 = encodeFour b ∧
      readFour tables 61 8 0 = encodeFour (if b = 0 then 18446744073709551615 else a / b) ∧
      readFour tables 61 12 0 = encodeFour (if b = 0 then a else a % b) := by
  by_cases zero : b = 0
  · subst b
    refine ⟨oneRowTables 61 123 (unsigned64ZeroWitness a),unsigned64_tables_fixed _,?_,?_,?_,?_⟩
    · exact unsigned64_one_row_slice_complete _ (unsigned64_zero_outside a)
        (unsigned64_zero_witness_bounds a aBound) (unsigned64_zero_witness_field a)
    · simp [oneRowTables]
    · rw [oneRowTables_read _ _ _ _ (by decide)]
      rfl
    · simpa only [↓reduceIte] using unsigned64_zero_columns a aBound
  · let q := a / b
    let r := a % b
    let w := b - r - 1
    have qBound : q < 18446744073709551616 := lt_of_le_of_lt (Nat.div_le_self _ _) aBound
    have remainderSmall : r < b := Nat.mod_lt _ (Nat.pos_of_ne_zero zero)
    have rBound : r < 18446744073709551616 := lt_trans remainderSmall bBound
    have wBound : w < 18446744073709551616 := by dsimp [w]; omega
    have identity : a = q * b + r := by
      simpa only [q,r,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div a b).symm
    have remainderBound : b = r + w + 1 := by dsimp [w]; omega
    refine ⟨oneRowTables 61 123 (unsigned64NonzeroWitness a b q r w),unsigned64_tables_fixed _,?_,?_,?_,?_⟩
    · exact unsigned64_one_row_slice_complete _ (unsigned64_nonzero_outside a b q r w)
        (unsigned64_nonzero_witness_bounds a b q r w aBound bBound qBound rBound wBound identity)
        (unsigned64_nonzero_witness_field a b q r w aBound bBound qBound rBound wBound identity remainderBound)
    · simp [oneRowTables]
    · rw [oneRowTables_read _ _ _ _ (by decide)]
      rfl
    · simpa only [zero,↓reduceIte] using unsigned64_nonzero_columns a b q r w aBound bBound qBound rBound

end DivRemFV

