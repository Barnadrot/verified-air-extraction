import DivRemFV.SignedTrace64Data

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def natFourList (d : Nat × Nat × Nat × Nat) : List Scalar :=
  [scalarOfNat d.1,scalarOfNat d.2.1,scalarOfNat d.2.2.1,scalarOfNat d.2.2.2]

theorem signed64_call_absA (a b : Nat) (cap : a < 18446744073709551616) : c11984.Holds (signed64Tables a b) := by
  unfold c11984
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed64Tables,witnessTables,signed64Rows] using inside
    omega
  subst row
  refine ⟨0,by simp [signed64Tables,witnessTables,signed64Rows],?_,?_⟩
  · simp [Port.Active,signed64_read_absA,absolute64Row,absolute64Witness,scalarOfNat,fieldModulus]
  · norm_num only [Port.tuple]
    simp only [List.map_cons,List.map_nil,signed64_read_main,signed64_read_absA]
    exact congrArg (fun d => natFourList (digits64 a) ++ natFourList d) (absolute64_witness_digits a cap)

theorem signed64_call_absB (a b : Nat) (cap : b < 18446744073709551616) : c11985.Holds (signed64Tables a b) := by
  unfold c11985
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed64Tables,witnessTables,signed64Rows] using inside
    omega
  subst row
  refine ⟨1,by simp [signed64Tables,witnessTables,signed64Rows],?_,?_⟩
  · simp [Port.Active,signed64_read_absB,absolute64Row,absolute64Witness,scalarOfNat,fieldModulus]
  · norm_num only [Port.tuple]
    simp only [List.map_cons,List.map_nil,signed64_read_main,signed64_read_absB]
    exact congrArg (fun d => natFourList (digits64 b) ++ natFourList d) (absolute64_witness_digits b cap)

theorem signed64_call_unsigned (a b : Nat) : c11986.Holds (signed64Tables a b) := by
  unfold c11986
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed64Tables,witnessTables,signed64Rows] using inside
    omega
  subst row
  refine ⟨0,by simp [signed64Tables,witnessTables,signed64Rows],?_,?_⟩
  · by_cases zero : magnitudeNat 64 b=0 <;>
      simp [Port.Active,signed64_read_unsigned,unsigned64Row,zero,unsigned64ZeroWitness,unsigned64NonzeroWitness,scalarOfNat,fieldModulus]
  · norm_num only [Port.tuple]
    simp only [List.map_cons,List.map_nil,signed64_read_main,signed64_read_unsigned]
    by_cases zero : magnitudeNat 64 b=0 <;>
      simp [unsigned64Row,zero,unsigned64ZeroWitness,unsigned64NonzeroWitness,signed64Witness,signed64Q,signed64R,unsignedQ,unsignedR]

theorem signed64_call_negQ (a b : Nat) (cap : a < 18446744073709551616) : c11989.Holds (signed64Tables a b) := by
  unfold c11989
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed64Tables,witnessTables,signed64Rows] using inside
    omega
  subst row
  have selected : b≠0 ∧ signValue 64 a≠signValue 64 b := by
    by_contra off
    have check := (return_active (signed64Tables a b) 62 44 #[16,17,18,19,8,9,10,11] 0).1 active
    simp [signed64_read_main,signed64Witness,off,scalarOfNat] at check
  refine ⟨0,by simp [signed64Tables,witnessTables,signed64Rows],?_,?_⟩
  · simp [Port.Active,signed64_read_negQ,negation64Row,negation64Witness,scalarOfNat,fieldModulus]
  · norm_num only [Port.tuple]
    simp only [List.map_cons,List.map_nil,signed64_read_main,signed64_read_negQ,
      signed64Witness,if_neg selected.1,if_neg selected.2]
    exact congrArg (fun d => natFourList (digits64 (signed64Q a b)) ++ natFourList d)
      (negation64_witness_digits (signed64Q a b) (signed64Q_bound a b cap))

theorem signed64_call_negR (a b : Nat) (ab : a < 18446744073709551616) (bb : b < 18446744073709551616) :
    c11991.Holds (signed64Tables a b) := by
  unfold c11991
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed64Tables,witnessTables,signed64Rows] using inside
    omega
  subst row
  have selected : b≠0 ∧ signValue 64 a=1 := by
    by_contra off
    have check := (return_active (signed64Tables a b) 62 45 #[20,21,22,23,12,13,14,15] 0).1 active
    simp [signed64_read_main,signed64Witness,off,scalarOfNat] at check
  have negative : signValue 64 a≠0 := by rw [selected.2]; decide
  refine ⟨1,by simp [signed64Tables,witnessTables,signed64Rows],?_,?_⟩
  · simp [Port.Active,signed64_read_negR,negation64Row,negation64Witness,scalarOfNat,fieldModulus]
  · norm_num only [Port.tuple]
    simp only [List.map_cons,List.map_nil,signed64_read_main,signed64_read_negR,
      signed64Witness,if_neg selected.1,if_neg negative]
    exact congrArg (fun d => natFourList (digits64 (signed64R a b)) ++ natFourList d)
      (negation64_witness_digits (signed64R a b) (signed64R_bound a b ab bb))

end DivRemFV
