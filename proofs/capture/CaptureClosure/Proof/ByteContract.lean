module
public import CaptureClosure.Proof.ModelBytes

@[expose] public section
namespace Perennial.divremfv.internal.airdata.SourceCapture

theorem word_byte_values (n : Nat) (bounded : n < 2^64) :
    (u64Le (W64 n)).map BitVec.toNat = DivRemFV.CaptureSyntax.wordBytes n := by
  have Hword : (W64 n).toNat = n := by word
  simp only [u64Le,u64LeDef,Hword]
  simp [LittleEndian.split,DivRemFV.CaptureSyntax.wordBytes,Nat.div_div_eq_div_mul]

theorem all_byte_values (words : List Nat) (bounded : ∀ n ∈ words, n < 2^64) :
    (wireBytes words).map BitVec.toNat = DivRemFV.CaptureSyntax.byteValues words := by
  induction words with
  | nil => rfl
  | cons n rest ih =>
    have hn := bounded n (by simp)
    have hr := ih (fun k member => bounded k (by simp [member]))
    simpa only [wireBytes_cons,DivRemFV.CaptureSyntax.byteValues,List.flatMap_cons,
      List.map_append,word_byte_values n hn] using congrArg
        ((DivRemFV.CaptureSyntax.wordBytes n) ++ ·) hr

#print axioms word_byte_values
#print axioms all_byte_values
end Perennial.divremfv.internal.airdata.SourceCapture
