import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M89 : Module := ⟨89, [36,114,97,110,103,101,95,117,55], true, false, [⟨0, [118,97,108,117,101], (some (7)), false, true, false⟩], ((List.range 128).map (fun n => [n]))⟩

def M89p0 : List Nat := [89,9,36,114,97,110,103,101,95,117,55,1,0,0,0,1,0,5,118,97,108,117,101,1,7,0,0,1,0,0,0,128]
theorem M89p0bound : M89p0.all wordBound = true := (by decide : [89,9,36,114,97,110,103,101,95,117,55,1,0,0,0,1,0,5,118,97,108,117,101,1,7,0,0,1,0,0,0,128].all wordBound = true)

def M89p1 : List Nat := ((List.range' 0 128).flatMap (fun n => [1,n]))
theorem M89p1bound : M89p1.all wordBound = true := (pairRangeBound 0 128 (by decide))

def M89words : List Nat := M89p0 ++ M89p1

theorem M89wire : module.encode M89 = M89words := by
  rw [module_fast]
  rfl

theorem M89wordBound : M89words.all wordBound = true := by
  simp only [M89words,List.all_append,M89p0bound,M89p1bound]
  try rfl

theorem M89bounded : ∀ n ∈ M89words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M89wordBound

end DivRemFV.Replay
