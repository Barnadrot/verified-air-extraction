import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M85 : Module := ⟨85, [36,114,97,110,103,101,95,117,51], true, false, [⟨0, [118,97,108,117,101], (some (3)), false, true, false⟩], ((List.range 8).map (fun n => [n]))⟩

def M85p0 : List Nat := [85,9,36,114,97,110,103,101,95,117,51,1,0,0,0,1,0,5,118,97,108,117,101,1,3,0,0,1,0,0,0,8,1,0,1,1,1,2,1,3,1,4,1,5,1,6,1,7]
theorem M85p0bound : M85p0.all wordBound = true := (by decide : [85,9,36,114,97,110,103,101,95,117,51,1,0,0,0,1,0,5,118,97,108,117,101,1,3,0,0,1,0,0,0,8,1,0,1,1,1,2,1,3,1,4,1,5,1,6,1,7].all wordBound = true)

def M85words : List Nat := M85p0

theorem M85wire : module.encode M85 = M85words := by
  rw [module_fast]
  rfl

theorem M85wordBound : M85words.all wordBound = true := by
  simp only [M85words,List.all_append,M85p0bound]
  try rfl

theorem M85bounded : ∀ n ∈ M85words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M85wordBound

end DivRemFV.Replay
