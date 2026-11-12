import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M90 : Module := ⟨90, [36,114,97,110,103,101,95,117,56], true, false, [⟨0, [118,97,108,117,101], (some (8)), false, true, false⟩], ((List.range 256).map (fun n => [n]))⟩

def M90p0 : List Nat := [90,9,36,114,97,110,103,101,95,117,56,1,0,0,0,1,0,5,118,97,108,117,101,1,8,0,0,1,0,0,0,256]
theorem M90p0bound : M90p0.all wordBound = true := (by decide : [90,9,36,114,97,110,103,101,95,117,56,1,0,0,0,1,0,5,118,97,108,117,101,1,8,0,0,1,0,0,0,256].all wordBound = true)

def M90p1 : List Nat := ((List.range' 0 256).flatMap (fun n => [1,n]))
theorem M90p1bound : M90p1.all wordBound = true := (pairRangeBound 0 256 (by decide))

def M90words : List Nat := M90p0 ++ M90p1

theorem M90wire : module.encode M90 = M90words := by
  rw [module_fast]
  rfl

theorem M90wordBound : M90words.all wordBound = true := by
  simp only [M90words,List.all_append,M90p0bound,M90p1bound]
  try rfl

theorem M90bounded : ∀ n ∈ M90words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M90wordBound

end DivRemFV.Replay
