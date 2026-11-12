import DivRemFV.ArtifactBinding
import DivRemFV.WriteBytes
import DivRemFV.FastEncode

namespace DivRemFV.Replay

def wordBound (n : Nat) : Bool := decide (n < 2^64)

theorem rangeBound (start count : Nat) (small : start + count ≤ 2^64) :
    (List.range' start count).all wordBound = true := by
  apply List.all_eq_true.mpr
  intro n member
  have h := List.mem_range'_1.mp member
  simp only [wordBound, decide_eq_true_eq]
  omega

theorem pairRangeBound (start count : Nat) (small : start + count ≤ 2^64) :
    ((List.range' start count).flatMap (fun n => [1,n])).all wordBound = true := by
  apply List.all_eq_true.mpr
  intro n member
  obtain ⟨i, inside, hn⟩ := List.mem_flatMap.mp member
  have hi := List.mem_range'_1.mp inside
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl <;> simp only [wordBound, decide_eq_true_eq] <;> omega

end DivRemFV.Replay
