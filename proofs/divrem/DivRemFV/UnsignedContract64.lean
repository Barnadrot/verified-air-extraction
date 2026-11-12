import DivRemFV.UnsignedComplete64

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def unsigned64Target : Port :=
  match c11986 with
  | .lookup _ [target] => target
  | _ => ⟨0,none,#[]⟩

theorem unsigned64Target_shape :
    unsigned64Target = ⟨61,some 121,#[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]⟩ := rfl

def fourList (value : Scalar × Scalar × Scalar × Scalar) : List Scalar :=
  [value.1,value.2.1,value.2.2.1,value.2.2.2]

def unsigned64Accepts (a b q r : Scalar × Scalar × Scalar × Scalar) : Prop :=
  ∃ tables : Tables,StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
    fourList a ++ fourList b ++ fourList q ++ fourList r ∈ unsigned64Target.messages tables

theorem four_encode_value (value : Nat) (bounded : value < 18446744073709551616) :
    281474976710656 * (encodeFour value).1.val + 4294967296 * (encodeFour value).2.1.val +
      65536 * (encodeFour value).2.2.1.val + (encodeFour value).2.2.2.val = value := by
  have packing := split16_64 value
  dsimp [encodeFour,encodeLimb]
  omega

theorem unsigned64_target_member (tables : Tables) (row : Nat)
    (inside : row < (tables 61).size) (active : readCell tables 61 121 row ≠ 0)
    (a b q r : Scalar × Scalar × Scalar × Scalar)
    (inputA : readFour tables 61 0 row = a) (inputB : readFour tables 61 4 row = b)
    (outputQ : readFour tables 61 8 row = q) (outputR : readFour tables 61 12 row = r) :
    fourList a ++ fourList b ++ fourList q ++ fourList r ∈ unsigned64Target.messages tables := by
  apply (Port.member_iff tables unsigned64Target _).2
  refine ⟨row,inside,?_,?_⟩
  · rw [unsigned64Target_shape]
    exact (return_active tables 61 121 _ row).2 active
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
    change [readCell tables 61 0 row,readCell tables 61 1 row,readCell tables 61 2 row,readCell tables 61 3 row,readCell tables 61 4 row,readCell tables 61 5 row,readCell tables 61 6 row,readCell tables 61 7 row,readCell tables 61 8 row,readCell tables 61 9 row,readCell tables 61 10 row,readCell tables 61 11 row,readCell tables 61 12 row,readCell tables 61 13 row,readCell tables 61 14 row,readCell tables 61 15 row] =
      [a.1,a.2.1,a.2.2.1,a.2.2.2,b.1,b.2.1,b.2.2.1,b.2.2.2,q.1,q.2.1,q.2.2.1,q.2.2.2,r.1,r.2.1,r.2.2.1,r.2.2.2]
    rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15]

theorem unsigned64_component_iff (a b : Nat) (aBound : a < 18446744073709551616)
    (bBound : b < 18446744073709551616) (q r : Scalar × Scalar × Scalar × Scalar) :
    unsigned64Accepts (encodeFour a) (encodeFour b) q r ↔
      q = encodeFour (if b = 0 then 18446744073709551615 else a / b) ∧
      r = encodeFour (if b = 0 then a else a % b) := by
  constructor
  · rintro ⟨tables,fixed,accepted,member⟩
    obtain ⟨row,inside,active,bindings⟩ := (Port.member_iff tables unsigned64Target _).1 member
    have gate : readCell tables 61 121 row ≠ 0 := by
      rw [unsigned64Target_shape] at active
      exact (return_active tables 61 121 _ row).1 active
    change row < (tables 61).size at inside
    change [readCell tables 61 0 row,readCell tables 61 1 row,readCell tables 61 2 row,readCell tables 61 3 row,readCell tables 61 4 row,readCell tables 61 5 row,readCell tables 61 6 row,readCell tables 61 7 row,readCell tables 61 8 row,readCell tables 61 9 row,readCell tables 61 10 row,readCell tables 61 11 row,readCell tables 61 12 row,readCell tables 61 13 row,readCell tables 61 14 row,readCell tables 61 15 row] =
      [(encodeFour a).1,(encodeFour a).2.1,(encodeFour a).2.2.1,(encodeFour a).2.2.2,(encodeFour b).1,(encodeFour b).2.1,(encodeFour b).2.2.1,(encodeFour b).2.2.2,q.1,q.2.1,q.2.2.1,q.2.2.2,r.1,r.2.1,r.2.2.1,r.2.2.2] at bindings
    simp only [List.cons.injEq,and_true] at bindings
    obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := bindings
    have inputA : wordValue (fun col => (readCell tables 61 col row).val) 0 = a := by
      dsimp [wordValue]
      rw [h0,h1,h2,h3]
      exact four_encode_value a aBound
    have inputB : wordValue (fun col => (readCell tables 61 col row).val) 4 = b := by
      dsimp [wordValue]
      rw [h4,h5,h6,h7]
      exact four_encode_value b bBound
    have result := unsigned64_air_columns tables row inside accepted fixed gate
    dsimp only at result
    rw [inputA,inputB] at result
    simpa only [h8,h9,h10,h11,h12,h13,h14,h15,Prod.eta] using result
  · rintro ⟨rfl,rfl⟩
    obtain ⟨tables,fixed,accepted,inside,active,aColumns,bColumns,qColumns,rColumns⟩ :=
      unsigned64_slice_exists a b aBound bBound
    refine ⟨tables,fixed,accepted,?_⟩
    apply unsigned64_target_member tables 0 inside
      (by change readCell tables 61 121 0 ≠ 0; rw [active]; decide) _ _ _ _
      aColumns bColumns qColumns rColumns

theorem unsigned64_false_remainder_rejected :
    ¬unsigned64Accepts (encodeFour 0) (encodeFour 2) (encodeFour 0) (encodeFour 1) := by
  rw [unsigned64_component_iff 0 2 (by decide) (by decide)]
  decide

end DivRemFV

