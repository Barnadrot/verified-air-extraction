import DivRemFV.SignExtension

namespace DivRemFV

def signExtensionTables (a : Nat) := oneRowTables 67 10 (signExtensionWitness (a/65536) (a%65536))

theorem signExtension_tables_fixed (a : Nat) : StaticTablesFixed (signExtensionTables a) := by
  apply oneRowTables_fixed
  intro bits
  simp [rangeTablePairs]

theorem signExtension_slice_complete (a : Nat) (cap : a < 4294967296) :
    ConstraintsHold (signExtensionTables a) Extension.constraints := by
  apply Extension.constraints_from_modules
  apply Extension.rows67_complete _ (signExtension_tables_fixed a)
  · intro row inside
    have zero : row=0 := by simp only [signExtensionTables,oneRowTables,↓reduceIte,Array.size_singleton] at inside; omega
    subst row
    apply Extension.bounds67_of_le _ _
      (signExtension_witness_bounds (a/65536) (a%65536) (by omega) (Nat.mod_lt _ (by decide)))
    intro col
    change (readCell (oneRowTables 67 10 (signExtensionWitness (a/65536) (a%65536))) 67 col 0).val ≤ _
    rw [oneRowTables_read_nat _ _ _ _ (signExtension_witness_outside _ _)]
    exact Nat.mod_le _ _
  · intro row inside
    have zero : row=0 := by simp only [signExtensionTables,oneRowTables,↓reduceIte,Array.size_singleton] at inside; omega
    subst row
    change Extension.Equations67 (fun col => ((readCell (oneRowTables 67 10 (signExtensionWitness (a/65536) (a%65536))) 67 col 0).val : K))
    have equal := funext (oneRowTables_read_field 67 10 · (signExtensionWitness (a/65536) (a%65536))
      (signExtension_witness_outside _ _))
    rw [equal]
    exact signExtension_witness_field _ _ (by omega) (Nat.mod_lt _ (by decide))

theorem signExtension_input_columns (a : Nat) (cap : a < 4294967296) :
    (readCell (signExtensionTables a) 67 0 0,readCell (signExtensionTables a) 67 1 0) = encodePair a := by
  unfold signExtensionTables
  rw [oneRowTables_read 67 10 0 _ (by decide),oneRowTables_read 67 10 1 _ (by decide)]
  exact scalarPairOfNat a cap

theorem signExtension_slice_exists (a : BitVec 32) :
    ∃ tables : Tables,StaticTablesFixed tables ∧ ConstraintsHold tables Extension.constraints ∧
      0 < (tables 67).size ∧ readCell tables 67 9 0 = 1 ∧
      (readCell tables 67 0 0,readCell tables 67 1 0) = encodePair a.toNat ∧
      readFour tables 67 2 0 = encodeFour (a.signExtend 64).toNat := by
  let tables := signExtensionTables a.toNat
  have fixed := signExtension_tables_fixed a.toNat
  have accepted := signExtension_slice_complete a.toNat a.isLt
  have inside : 0 < (tables 67).size := by simp [tables,signExtensionTables,oneRowTables]
  have active : readCell tables 67 9 0 = 1 := by
    dsimp only [tables,signExtensionTables]
    rw [oneRowTables_read 67 10 9 _ (by decide)]
    rfl
  have input := signExtension_input_columns a.toNat a.isLt
  have output := signExtension_air_columns tables 0 inside accepted fixed
    (by change readCell tables 67 9 0 ≠ 0; rw [active]; decide) a input
  exact ⟨tables,fixed,accepted,inside,active,input,output⟩

end DivRemFV
