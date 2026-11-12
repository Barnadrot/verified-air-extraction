import DivRemFV.SignedComplete32
import DivRemFV.Generated.Incoming

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def joinCallTargets (left right : Port) (inputs : Nat) : Port :=
  { left with columns := left.columns ++ right.columns.extract inputs right.columns.size }

def signed32Target : Port := joinCallTargets (callTarget incoming9645) (callTarget incoming9651) 4

theorem signed32Target_shape : signed32Target = ⟨64,some 23,#[0,1,2,3,4,5,6,7]⟩ := by decide

def signed32Accepts (a b q r : Scalar × Scalar) : Prop :=
  ∃ tables : Tables,StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
    [a.1,a.2,b.1,b.2,q.1,q.2,r.1,r.2] ∈ signed32Target.messages tables

theorem signed32_target_member (tables : Tables) (row : Nat)
    (inside : row < (tables 64).size) (active : readCell tables 64 23 row ≠ 0)
    (a b q r : Scalar × Scalar)
    (inputA : (readCell tables 64 0 row,readCell tables 64 1 row) = a)
    (inputB : (readCell tables 64 2 row,readCell tables 64 3 row) = b)
    (outputQ : (readCell tables 64 4 row,readCell tables 64 5 row) = q)
    (outputR : (readCell tables 64 6 row,readCell tables 64 7 row) = r) :
    [a.1,a.2,b.1,b.2,q.1,q.2,r.1,r.2] ∈ signed32Target.messages tables := by
  apply (Port.member_iff tables signed32Target _).2
  refine ⟨row,inside,?_,?_⟩
  · rw [signed32Target_shape]
    exact (return_active tables 64 23 _ row).2 active
  · have a0 := congrArg Prod.fst inputA
    have a1 := congrArg Prod.snd inputA
    have b0 := congrArg Prod.fst inputB
    have b1 := congrArg Prod.snd inputB
    have q0 := congrArg Prod.fst outputQ
    have q1 := congrArg Prod.snd outputQ
    have r0 := congrArg Prod.fst outputR
    have r1 := congrArg Prod.snd outputR
    simp only [Prod.fst,Prod.snd] at a0 a1 b0 b1 q0 q1 r0 r1
    change [readCell tables 64 0 row,readCell tables 64 1 row,
      readCell tables 64 2 row,readCell tables 64 3 row,
      readCell tables 64 4 row,readCell tables 64 5 row,
      readCell tables 64 6 row,readCell tables 64 7 row] = _
    rw [a0,a1,b0,b1,q0,q1,r0,r1]

theorem signed32_component_iff (a b : BitVec 32) (q r : Scalar × Scalar) :
    signed32Accepts (encodePair a.toNat) (encodePair b.toNat) q r ↔
      q = encodePair (signedQuotient a b).toNat ∧ r = encodePair (signedRemainder a b).toNat := by
  constructor
  · rintro ⟨tables,fixed,accepted,member⟩
    obtain ⟨row,inside,active,bindings⟩ := (Port.member_iff tables signed32Target _).1 member
    have gate : readCell tables 64 23 row ≠ 0 := by
      rw [signed32Target_shape] at active
      exact (return_active tables 64 23 _ row).1 active
    change row < (tables 64).size at inside
    change [readCell tables 64 0 row,readCell tables 64 1 row,
      readCell tables 64 2 row,readCell tables 64 3 row,
      readCell tables 64 4 row,readCell tables 64 5 row,
      readCell tables 64 6 row,readCell tables 64 7 row] =
        [(encodePair a.toNat).1,(encodePair a.toNat).2,(encodePair b.toNat).1,(encodePair b.toNat).2,q.1,q.2,r.1,r.2] at bindings
    simp only [List.cons.injEq, and_true] at bindings
    obtain ⟨a0,a1,b0,b1,q0,q1,r0,r1⟩ := bindings
    have inputA : pairValue (fun col => (readCell tables 64 col row).val) 0 1 = a.toNat := by
      dsimp [pairValue]
      rw [a0,a1]
      exact pair_encode_value a.toNat a.isLt
    have inputB : pairValue (fun col => (readCell tables 64 col row).val) 2 3 = b.toNat := by
      dsimp [pairValue]
      rw [b0,b1]
      exact pair_encode_value b.toNat b.isLt
    have result := signed32_air_columns tables row inside accepted fixed gate a b inputA inputB
    simpa only [q0,q1,r0,r1,Prod.eta] using result
  · rintro ⟨rfl,rfl⟩
    obtain ⟨tables,fixed,accepted,inside,active,aColumns,bColumns,qColumns,rColumns⟩ :=
      signed32_slice_exists a b
    refine ⟨tables,fixed,accepted,?_⟩
    apply signed32_target_member tables 0 inside
      (by change readCell tables 64 23 0 ≠ 0; rw [active]; decide) _ _ _ _
      aColumns bColumns qColumns rColumns


end DivRemFV


