import DivRemFV.UnsignedComplete32

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def unsigned32Target : Port :=
  match c12116 with
  | .lookup _ [target] => target
  | _ => ⟨0,none,#[]⟩

theorem unsigned32Target_shape :
    unsigned32Target = ⟨63,some 51,#[0,1,2,3,4,5,6,7]⟩ := rfl

def unsigned32Accepts (a b q r : Scalar × Scalar) : Prop :=
  ∃ tables : Tables, StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
    [a.1,a.2,b.1,b.2,q.1,q.2,r.1,r.2] ∈ unsigned32Target.messages tables

theorem pair_encode_value (value : Nat) (bounded : value < 4294967296) :
    65536 * (encodePair value).1.val + (encodePair value).2.val = value := by
  dsimp [encodePair, encodeLimb]
  omega

theorem unsigned32_target_member (tables : Tables) (row : Nat)
    (inside : row < (tables 63).size) (active : readCell tables 63 51 row ≠ 0)
    (a b q r : Scalar × Scalar)
    (inputA : (readCell tables 63 0 row,readCell tables 63 1 row) = a)
    (inputB : (readCell tables 63 2 row,readCell tables 63 3 row) = b)
    (outputQ : (readCell tables 63 4 row,readCell tables 63 5 row) = q)
    (outputR : (readCell tables 63 6 row,readCell tables 63 7 row) = r) :
    [a.1,a.2,b.1,b.2,q.1,q.2,r.1,r.2] ∈ unsigned32Target.messages tables := by
  apply (Port.member_iff tables unsigned32Target _).2
  refine ⟨row,inside,?_,?_⟩
  · rw [unsigned32Target_shape]
    exact (return_active tables 63 51 _ row).2 active
  · have a0 := congrArg Prod.fst inputA
    have a1 := congrArg Prod.snd inputA
    have b0 := congrArg Prod.fst inputB
    have b1 := congrArg Prod.snd inputB
    have q0 := congrArg Prod.fst outputQ
    have q1 := congrArg Prod.snd outputQ
    have r0 := congrArg Prod.fst outputR
    have r1 := congrArg Prod.snd outputR
    simp only [Prod.fst,Prod.snd] at a0 a1 b0 b1 q0 q1 r0 r1
    change [readCell tables 63 0 row,readCell tables 63 1 row,
      readCell tables 63 2 row,readCell tables 63 3 row,
      readCell tables 63 4 row,readCell tables 63 5 row,
      readCell tables 63 6 row,readCell tables 63 7 row] = _
    rw [a0,a1,b0,b1,q0,q1,r0,r1]

theorem unsigned32_slice_exists (a b : Nat) (aBound : a < 4294967296) (bBound : b < 4294967296) :
    ∃ tables : Tables, StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
      0 < (tables 63).size ∧ readCell tables 63 51 0 = 1 ∧
      (readCell tables 63 0 0,readCell tables 63 1 0) = encodePair a ∧
      (readCell tables 63 2 0,readCell tables 63 3 0) = encodePair b ∧
      (readCell tables 63 4 0,readCell tables 63 5 0) =
        encodePair (if b = 0 then 4294967295 else a / b) ∧
      (readCell tables 63 6 0,readCell tables 63 7 0) =
        encodePair (if b = 0 then a else a % b) := by
  by_cases zero : b = 0
  · subst b
    simpa only [↓reduceIte] using unsigned32_zero_slice_exists a aBound
  · simpa only [zero, ↓reduceIte] using unsigned32_nonzero_slice_exists a b aBound bBound zero

theorem unsigned32_component_iff (a b : Nat) (aBound : a < 4294967296)
    (bBound : b < 4294967296) (q r : Scalar × Scalar) :
    unsigned32Accepts (encodePair a) (encodePair b) q r ↔
      q = encodePair (if b = 0 then 4294967295 else a / b) ∧
      r = encodePair (if b = 0 then a else a % b) := by
  constructor
  · rintro ⟨tables,fixed,accepted,member⟩
    obtain ⟨row,inside,active,bindings⟩ := (Port.member_iff tables unsigned32Target _).1 member
    have gate : readCell tables 63 51 row ≠ 0 := by
      rw [unsigned32Target_shape] at active
      exact (return_active tables 63 51 _ row).1 active
    change row < (tables 63).size at inside
    change [readCell tables 63 0 row,readCell tables 63 1 row,
      readCell tables 63 2 row,readCell tables 63 3 row,
      readCell tables 63 4 row,readCell tables 63 5 row,
      readCell tables 63 6 row,readCell tables 63 7 row] =
        [(encodePair a).1,(encodePair a).2,(encodePair b).1,(encodePair b).2,q.1,q.2,r.1,r.2] at bindings
    simp only [List.cons.injEq, and_true] at bindings
    obtain ⟨a0,a1,b0,b1,q0,q1,r0,r1⟩ := bindings
    have inputA : pairValue (fun col => (readCell tables 63 col row).val) 0 1 = a := by
      dsimp [pairValue]
      rw [a0,a1]
      exact pair_encode_value a aBound
    have inputB : pairValue (fun col => (readCell tables 63 col row).val) 2 3 = b := by
      dsimp [pairValue]
      rw [b0,b1]
      exact pair_encode_value b bBound
    have result := unsigned32_air_columns tables row inside accepted fixed gate
    dsimp only at result
    rw [inputA,inputB] at result
    simpa only [q0,q1,r0,r1,Prod.eta] using result
  · rintro ⟨rfl,rfl⟩
    obtain ⟨tables,fixed,accepted,inside,active,aColumns,bColumns,qColumns,rColumns⟩ :=
      unsigned32_slice_exists a b aBound bBound
    refine ⟨tables,fixed,accepted,?_⟩
    apply unsigned32_target_member tables 0 inside
      (by change readCell tables 63 51 0 ≠ 0; rw [active]; decide) _ _ _ _
      aColumns bColumns qColumns rColumns

theorem unsigned32_false_remainder_rejected :
    ¬unsigned32Accepts (encodePair 0) (encodePair 2) (encodePair 0) (encodePair 1) := by
  rw [unsigned32_component_iff 0 2 (by decide) (by decide)]
  decide

end DivRemFV

