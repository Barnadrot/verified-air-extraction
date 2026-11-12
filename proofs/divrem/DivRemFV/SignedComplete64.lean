import DivRemFV.SignedTrace64Calls
import DivRemFV.SignedColumns

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

theorem signed64_slice_complete (a b : Nat) (ab : a < 18446744073709551616) (bb : b < 18446744073709551616) :
    ConstraintsHold (signed64Tables a b) constraints := by
  apply constraints_from_modules
  · apply witness_rows55_complete (signed64Rows a b)
    · intro row inside
      have cases : row=0 ∨ row=1 := by simp [signed64Rows] at inside; omega
      rcases cases with rfl | rfl
      · simpa [signed64Rows] using (absolute64_row_valid a ab).1
      · simpa [signed64Rows] using (absolute64_row_valid b bb).1
    · intro row inside
      have cases : row=0 ∨ row=1 := by simp [signed64Rows] at inside; omega
      rcases cases with rfl | rfl
      · simpa [signed64Rows] using (absolute64_row_valid a ab).2
      · simpa [signed64Rows] using (absolute64_row_valid b bb).2
  · apply witness_rows56_complete (signed64Rows a b)
    all_goals intro row inside; simp [signed64Rows] at inside
  · apply witness_rows61_complete (signed64Rows a b)
    · intro row inside
      have zero : row=0 := by simp only [signed64Rows,Array.size_singleton] at inside; omega
      subst row
      exact (unsigned64_row_valid _ _ (magnitude64_bound a ab) (magnitude64_bound b bb)).1
    · intro row inside
      have zero : row=0 := by simp only [signed64Rows,Array.size_singleton] at inside; omega
      subst row
      exact (unsigned64_row_valid _ _ (magnitude64_bound a ab) (magnitude64_bound b bb)).2
  · apply witness_rows62_complete (signed64Rows a b)
    · intro row inside
      have zero : row=0 := by simp only [signed64Rows,Array.size_singleton] at inside; omega
      subst row
      exact signed64_witness_bounds _ _ _ _ ab bb (signed64Q_bound a b ab) (signed64R_bound a b ab bb)
    · intro row inside
      have zero : row=0 := by simp only [signed64Rows,Array.size_singleton] at inside; omega
      subst row
      exact signed64_witness_field _ _ _ _ ab bb
    · exact signed64_call_absA a b ab
    · exact signed64_call_absB a b bb
    · exact signed64_call_unsigned a b
    · exact signed64_call_negQ a b ab
    · exact signed64_call_negR a b ab bb
  · apply witness_rows63_complete (signed64Rows a b)
    all_goals intro row inside; simp [signed64Rows] at inside
  · apply witness_rows64_complete (signed64Rows a b)
    · intro row inside; simp [signed64Rows] at inside
    · intro row inside; simp [signed64Rows] at inside
    · intro message member; simp [c12114,messages,Port.messages,witnessTables,signed64Rows] at member
    · intro message member; simp [c12115,messages,Port.messages,witnessTables,signed64Rows] at member
    · intro message member; simp [c12116,messages,Port.messages,witnessTables,signed64Rows] at member
    · intro message member; simp [c12119,messages,Port.messages,witnessTables,signed64Rows] at member
    · intro message member; simp [c12121,messages,Port.messages,witnessTables,signed64Rows] at member
  · apply witness_rows65_complete (signed64Rows a b)
    · intro row inside
      have cases : row=0 ∨ row=1 := by simp [signed64Rows] at inside; omega
      rcases cases with rfl | rfl
      · simpa [signed64Rows] using (negation64_row_valid _ (signed64Q_bound a b ab)).1
      · simpa [signed64Rows] using (negation64_row_valid _ (signed64R_bound a b ab bb)).1
    · intro row inside
      have cases : row=0 ∨ row=1 := by simp [signed64Rows] at inside; omega
      rcases cases with rfl | rfl
      · simpa [signed64Rows] using (negation64_row_valid _ (signed64Q_bound a b ab)).2
      · simpa [signed64Rows] using (negation64_row_valid _ (signed64R_bound a b ab bb)).2
  · apply witness_rows66_complete (signed64Rows a b)
    all_goals intro row inside; simp [signed64Rows] at inside

theorem readFour_value (tables : Tables) (mid start row value : Nat)
    (cap : value < 18446744073709551616) (input : readFour tables mid start row = encodeFour value) :
    wordValue (fun col => (readCell tables mid col row).val) start = value := by
  have packing := congrArg (fun d : Scalar × Scalar × Scalar × Scalar =>
    281474976710656*d.1.val+4294967296*d.2.1.val+65536*d.2.2.1.val+d.2.2.2.val) input
  exact packing.trans (four_encode_value value cap)

theorem signed64_input_columns (a b : Nat) (ab : a < 18446744073709551616) (bb : b < 18446744073709551616) :
    readFour (signed64Tables a b) 62 0 0 = encodeFour a ∧
    readFour (signed64Tables a b) 62 4 0 = encodeFour b := by
  simp only [readFour,signed64_read_main]
  exact ⟨scalarFourOfNat a ab,scalarFourOfNat b bb⟩

theorem signed64_slice_exists (a b : BitVec 64) :
    ∃ tables : Tables,StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
      0 < (tables 62).size ∧ readCell tables 62 43 0 = 1 ∧
      readFour tables 62 0 0 = encodeFour a.toNat ∧ readFour tables 62 4 0 = encodeFour b.toNat ∧
      readFour tables 62 8 0 = encodeFour (signedQuotient a b).toNat ∧
      readFour tables 62 12 0 = encodeFour (signedRemainder a b).toNat := by
  let tables := signed64Tables a.toNat b.toNat
  have accepted := signed64_slice_complete a.toNat b.toNat a.isLt b.isLt
  have fixed := witnessTables_fixed (signed64Rows a.toNat b.toNat)
  have inside : 0 < (tables 62).size := by simp [tables,signed64Tables,witnessTables,signed64Rows]
  have active : readCell tables 62 43 0 = 1 := by rw [signed64_read_main]; rfl
  have inputs := signed64_input_columns a.toNat b.toNat a.isLt b.isLt
  have outputs := signed64_air_columns tables 0 inside accepted fixed
    (by change readCell tables 62 43 0 ≠ 0; rw [active]; decide) a b
    (readFour_value tables 62 0 0 a.toNat a.isLt inputs.1)
    (readFour_value tables 62 4 0 b.toNat b.isLt inputs.2)
  exact ⟨tables,fixed,accepted,inside,active,inputs.1,inputs.2,outputs.1,outputs.2⟩

end DivRemFV
