import DivRemFV.ReplaySupport

namespace DivRemFV.Replay

def byteTableRow (n : Nat) : List Nat :=
  let a := BitVec.ofNat 8 (n / 256)
  let b := BitVec.ofNat 8 (n % 256)
  [a.toNat,b.toNat,(a &&& b).toNat,(a ||| b).toNat,(a ^^^ b).toNat]

theorem byteTableRow_length (n : Nat) : (byteTableRow n).length = 5 := rfl

theorem byteTableRow_fast (n : Nat) :
    ArtifactWire.natListWords (byteTableRow n) = 5 :: byteTableRow n := rfl

theorem byteTableRow_bounded (n : Nat) : (5 :: byteTableRow n).all wordBound = true := by
  let a := BitVec.ofNat 8 (n / 256)
  let b := BitVec.ofNat 8 (n % 256)
  have ha := a.isLt
  have hb := b.isLt
  have hab := (a &&& b).isLt
  have hao := (a ||| b).isLt
  have hax := (a ^^^ b).isLt
  simp only [byteTableRow,List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,
    wordBound,decide_eq_true_eq]
  change 5 < 2^64 ∧ a.toNat < 2^64 ∧ b.toNat < 2^64 ∧
    (a &&& b).toNat < 2^64 ∧ (a ||| b).toNat < 2^64 ∧ (a ^^^ b).toNat < 2^64
  omega

theorem byteTable_bounded (count : Nat) :
    ((List.range count).flatMap (fun n => 5 :: byteTableRow n)).all wordBound = true := by
  apply List.all_eq_true.mpr
  intro value member
  obtain ⟨n,_,inside⟩ := List.mem_flatMap.mp member
  exact List.all_eq_true.mp (byteTableRow_bounded n) value inside

end DivRemFV.Replay
