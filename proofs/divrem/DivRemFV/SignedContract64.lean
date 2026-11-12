import DivRemFV.SignedComplete64
import DivRemFV.SignedContract32

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def signed64Target : Port := joinCallTargets (callTarget incoming9618) (callTarget incoming9622) 8

theorem signed64Target_shape :
    signed64Target = ⟨62,some 43,#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]⟩ := by decide

def signed64Accepts (a b q r : Scalar × Scalar × Scalar × Scalar) : Prop :=
  ∃ tables : Tables,StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
    fourList a ++ fourList b ++ fourList q ++ fourList r ∈ signed64Target.messages tables

theorem signed64_target_member (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (active : readCell tables 62 43 row ≠ 0)
    (a b q r : Scalar × Scalar × Scalar × Scalar)
    (inputA : readFour tables 62 0 row = a) (inputB : readFour tables 62 4 row = b)
    (outputQ : readFour tables 62 8 row = q) (outputR : readFour tables 62 12 row = r) :
    fourList a ++ fourList b ++ fourList q ++ fourList r ∈ signed64Target.messages tables := by
  apply (Port.member_iff tables signed64Target _).2
  refine ⟨row,inside,?_,?_⟩
  · rw [signed64Target_shape]
    exact (return_active tables 62 43 _ row).2 active
  · have h0 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.1) inputA
    have h1 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.1) inputA
    have h2 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.2.1) inputA
    have h3 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.2.2) inputA
    have h4 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.1) inputB
    have h5 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.1) inputB
    have h6 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.2.1) inputB
    have h7 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.2.2) inputB
    have h8 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.1) outputQ
    have h9 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.1) outputQ
    have h10 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.2.1) outputQ
    have h11 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.2.2) outputQ
    have h12 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.1) outputR
    have h13 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.1) outputR
    have h14 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.2.1) outputR
    have h15 := congrArg (fun x : Scalar × Scalar × Scalar × Scalar => x.2.2.2) outputR
    simp only [readFour,Prod.fst,Prod.snd] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    change [readCell tables 62 0 row,readCell tables 62 1 row,readCell tables 62 2 row,readCell tables 62 3 row,readCell tables 62 4 row,readCell tables 62 5 row,readCell tables 62 6 row,readCell tables 62 7 row,readCell tables 62 8 row,readCell tables 62 9 row,readCell tables 62 10 row,readCell tables 62 11 row,readCell tables 62 12 row,readCell tables 62 13 row,readCell tables 62 14 row,readCell tables 62 15 row] =
      [a.1,a.2.1,a.2.2.1,a.2.2.2,b.1,b.2.1,b.2.2.1,b.2.2.2,q.1,q.2.1,q.2.2.1,q.2.2.2,r.1,r.2.1,r.2.2.1,r.2.2.2]
    rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15]

theorem signed64_component_iff (a b : BitVec 64) (q r : Scalar × Scalar × Scalar × Scalar) :
    signed64Accepts (encodeFour a.toNat) (encodeFour b.toNat) q r ↔
      q = encodeFour (signedQuotient a b).toNat ∧ r = encodeFour (signedRemainder a b).toNat := by
  constructor
  · rintro ⟨tables,fixed,accepted,member⟩
    obtain ⟨row,inside,active,bindings⟩ := (Port.member_iff tables signed64Target _).1 member
    have gate : readCell tables 62 43 row ≠ 0 := by
      rw [signed64Target_shape] at active
      exact (return_active tables 62 43 _ row).1 active
    change row < (tables 62).size at inside
    change [readCell tables 62 0 row,readCell tables 62 1 row,readCell tables 62 2 row,readCell tables 62 3 row,readCell tables 62 4 row,readCell tables 62 5 row,readCell tables 62 6 row,readCell tables 62 7 row,readCell tables 62 8 row,readCell tables 62 9 row,readCell tables 62 10 row,readCell tables 62 11 row,readCell tables 62 12 row,readCell tables 62 13 row,readCell tables 62 14 row,readCell tables 62 15 row] =
      [(encodeFour a.toNat).1,(encodeFour a.toNat).2.1,(encodeFour a.toNat).2.2.1,(encodeFour a.toNat).2.2.2,(encodeFour b.toNat).1,(encodeFour b.toNat).2.1,(encodeFour b.toNat).2.2.1,(encodeFour b.toNat).2.2.2,q.1,q.2.1,q.2.2.1,q.2.2.2,r.1,r.2.1,r.2.2.1,r.2.2.2] at bindings
    simp only [List.cons.injEq,and_true] at bindings
    obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := bindings
    have inputA : wordValue (fun col => (readCell tables 62 col row).val) 0 = a.toNat := by
      dsimp [wordValue]
      rw [h0,h1,h2,h3]
      exact four_encode_value a.toNat a.isLt
    have inputB : wordValue (fun col => (readCell tables 62 col row).val) 4 = b.toNat := by
      dsimp [wordValue]
      rw [h4,h5,h6,h7]
      exact four_encode_value b.toNat b.isLt
    have result := signed64_air_columns tables row inside accepted fixed gate a b inputA inputB
    simpa only [h8,h9,h10,h11,h12,h13,h14,h15,Prod.eta] using result
  · rintro ⟨rfl,rfl⟩
    obtain ⟨tables,fixed,accepted,inside,active,aColumns,bColumns,qColumns,rColumns⟩ :=
      signed64_slice_exists a b
    refine ⟨tables,fixed,accepted,?_⟩
    apply signed64_target_member tables 0 inside
      (by change readCell tables 62 43 0 ≠ 0; rw [active]; decide) _ _ _ _
      aColumns bColumns qColumns rColumns


end DivRemFV


