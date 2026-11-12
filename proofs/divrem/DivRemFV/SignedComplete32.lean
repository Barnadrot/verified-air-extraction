import DivRemFV.SignedTrace32Calls
import DivRemFV.SignedColumns

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

theorem signed32_slice_complete (a b : Nat) (ab : a < 4294967296) (bb : b < 4294967296) :
    ConstraintsHold (signed32Tables a b) constraints := by
  apply constraints_from_modules
  · apply witness_rows55_complete (signed32Rows a b)
    all_goals intro row inside; simp [signed32Rows] at inside
  · apply witness_rows56_complete (signed32Rows a b)
    · intro row inside
      have cases : row=0 ∨ row=1 := by simp [signed32Rows] at inside; omega
      rcases cases with rfl | rfl
      · simpa [signed32Rows] using (absolute32_row_valid a ab).1
      · simpa [signed32Rows] using (absolute32_row_valid b bb).1
    · intro row inside
      have cases : row=0 ∨ row=1 := by simp [signed32Rows] at inside; omega
      rcases cases with rfl | rfl
      · simpa [signed32Rows] using (absolute32_row_valid a ab).2
      · simpa [signed32Rows] using (absolute32_row_valid b bb).2
  · apply witness_rows61_complete (signed32Rows a b)
    all_goals intro row inside; simp [signed32Rows] at inside
  · apply witness_rows62_complete (signed32Rows a b)
    · intro row inside; simp [signed32Rows] at inside
    · intro row inside; simp [signed32Rows] at inside
    · intro message member; simp [c11984,messages,Port.messages,signed32Tables,witnessTables,signed32Rows] at member
    · intro message member; simp [c11985,messages,Port.messages,signed32Tables,witnessTables,signed32Rows] at member
    · intro message member; simp [c11986,messages,Port.messages,signed32Tables,witnessTables,signed32Rows] at member
    · intro message member; simp [c11989,messages,Port.messages,signed32Tables,witnessTables,signed32Rows] at member
    · intro message member; simp [c11991,messages,Port.messages,signed32Tables,witnessTables,signed32Rows] at member
  · apply witness_rows63_complete (signed32Rows a b)
    · intro row inside
      have zero : row=0 := by simp only [signed32Rows,Array.size_singleton] at inside; omega
      subst row
      exact (unsigned32_row_valid _ _ (magnitude32_bound a ab) (magnitude32_bound b bb)).1
    · intro row inside
      have zero : row=0 := by simp only [signed32Rows,Array.size_singleton] at inside; omega
      subst row
      exact (unsigned32_row_valid _ _ (magnitude32_bound a ab) (magnitude32_bound b bb)).2
  · apply witness_rows64_complete (signed32Rows a b)
    · intro row inside
      have zero : row=0 := by simp only [signed32Rows,Array.size_singleton] at inside; omega
      subst row
      exact signed32_witness_bounds _ _ _ _ ab bb (signed32Q_bound a b ab) (signed32R_bound a b ab bb)
    · intro row inside
      have zero : row=0 := by simp only [signed32Rows,Array.size_singleton] at inside; omega
      subst row
      exact signed32_witness_field _ _ _ _ ab bb
    · exact signed32_call_absA a b ab
    · exact signed32_call_absB a b bb
    · exact signed32_call_unsigned a b
    · exact signed32_call_negQ a b ab
    · exact signed32_call_negR a b ab bb
  · apply witness_rows65_complete (signed32Rows a b)
    all_goals intro row inside; simp [signed32Rows] at inside
  · apply witness_rows66_complete (signed32Rows a b)
    · intro row inside
      have cases : row=0 ∨ row=1 := by simp [signed32Rows] at inside; omega
      rcases cases with rfl | rfl
      · simpa [signed32Rows] using (negation32_row_valid _ (signed32Q_bound a b ab)).1
      · simpa [signed32Rows] using (negation32_row_valid _ (signed32R_bound a b ab bb)).1
    · intro row inside
      have cases : row=0 ∨ row=1 := by simp [signed32Rows] at inside; omega
      rcases cases with rfl | rfl
      · simpa [signed32Rows] using (negation32_row_valid _ (signed32Q_bound a b ab)).2
      · simpa [signed32Rows] using (negation32_row_valid _ (signed32R_bound a b ab bb)).2

theorem signed32_input_columns (a b : Nat) (ab : a < 4294967296) (bb : b < 4294967296) :
    (readCell (signed32Tables a b) 64 0 0,readCell (signed32Tables a b) 64 1 0) = encodePair a ∧
    (readCell (signed32Tables a b) 64 2 0,readCell (signed32Tables a b) 64 3 0) = encodePair b := by
  rw [signed32_read_main,signed32_read_main,signed32_read_main,signed32_read_main]
  exact ⟨scalarPairOfNat a ab,scalarPairOfNat b bb⟩

theorem signed32_slice_exists (a b : BitVec 32) :
    ∃ tables : Tables,StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
      0 < (tables 64).size ∧ readCell tables 64 23 0 = 1 ∧
      (readCell tables 64 0 0,readCell tables 64 1 0) = encodePair a.toNat ∧
      (readCell tables 64 2 0,readCell tables 64 3 0) = encodePair b.toNat ∧
      (readCell tables 64 4 0,readCell tables 64 5 0) = encodePair (signedQuotient a b).toNat ∧
      (readCell tables 64 6 0,readCell tables 64 7 0) = encodePair (signedRemainder a b).toNat := by
  let tables := signed32Tables a.toNat b.toNat
  have accepted := signed32_slice_complete a.toNat b.toNat a.isLt b.isLt
  have fixed := witnessTables_fixed (signed32Rows a.toNat b.toNat)
  have inside : 0 < (tables 64).size := by simp [tables,signed32Tables,witnessTables,signed32Rows]
  have active : readCell tables 64 23 0 = 1 := by
    rw [signed32_read_main]
    rfl
  have inputs := signed32_input_columns a.toNat b.toNat a.isLt b.isLt
  have inputA : pairValue (fun col => (readCell tables 64 col 0).val) 0 1 = a.toNat := by
    have high := congrArg (fun pair : Scalar × Scalar => pair.1.val) inputs.1
    have low := congrArg (fun pair : Scalar × Scalar => pair.2.val) inputs.1
    dsimp only at high low
    dsimp [pairValue]
    rw [high,low]
    exact pair_encode_value a.toNat a.isLt
  have inputB : pairValue (fun col => (readCell tables 64 col 0).val) 2 3 = b.toNat := by
    have high := congrArg (fun pair : Scalar × Scalar => pair.1.val) inputs.2
    have low := congrArg (fun pair : Scalar × Scalar => pair.2.val) inputs.2
    dsimp only at high low
    dsimp [pairValue]
    rw [high,low]
    exact pair_encode_value b.toNat b.isLt
  have outputs := signed32_air_columns tables 0 inside accepted fixed
    (by change readCell tables 64 23 0 ≠ 0; rw [active]; decide) a b inputA inputB
  exact ⟨tables,fixed,accepted,inside,active,inputs.1,inputs.2,outputs.1,outputs.2⟩

end DivRemFV

