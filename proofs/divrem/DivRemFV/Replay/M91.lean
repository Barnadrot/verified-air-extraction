import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M91 : Module := ⟨91, [36,114,97,110,103,101,95,117,57], true, false, [⟨0, [118,97,108,117,101], (some (9)), false, true, false⟩], ((List.range 512).map (fun n => [n]))⟩

def M91p0 : List Nat := [91,9,36,114,97,110,103,101,95,117,57,1,0,0,0,1,0,5,118,97,108,117,101,1,9,0,0,1,0,0,0,512]
theorem M91p0bound : M91p0.all wordBound = true := (by decide : [91,9,36,114,97,110,103,101,95,117,57,1,0,0,0,1,0,5,118,97,108,117,101,1,9,0,0,1,0,0,0,512].all wordBound = true)

def M91p1 : List Nat := ((List.range' 0 512).flatMap (fun n => [1,n]))
theorem M91p1bound : M91p1.all wordBound = true := (pairRangeBound 0 512 (by decide))

def M91words : List Nat := M91p0 ++ M91p1

theorem M91wire : module.encode M91 = M91words := by
  rw [module_fast]
  rfl

theorem M91wordBound : M91words.all wordBound = true := by
  simp only [M91words,List.all_append,M91p0bound,M91p1bound]
  try rfl

theorem M91bounded : ∀ n ∈ M91words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M91wordBound

end DivRemFV.Replay
