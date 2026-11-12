import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M86 : Module := ⟨86, [36,114,97,110,103,101,95,117,52], true, false, [⟨0, [118,97,108,117,101], (some (4)), false, true, false⟩], ((List.range 16).map (fun n => [n]))⟩

def M86p0 : List Nat := [86,9,36,114,97,110,103,101,95,117,52,1,0,0,0,1,0,5,118,97,108,117,101,1,4,0,0,1,0,0,0,16,1,0,1,1,1,2,1,3,1,4,1,5,1,6,1,7,1,8,1,9,1,10,1,11,1,12,1,13,1,14,1,15]
theorem M86p0bound : M86p0.all wordBound = true := (by decide : [86,9,36,114,97,110,103,101,95,117,52,1,0,0,0,1,0,5,118,97,108,117,101,1,4,0,0,1,0,0,0,16,1,0,1,1,1,2,1,3,1,4,1,5,1,6,1,7,1,8,1,9,1,10,1,11,1,12,1,13,1,14,1,15].all wordBound = true)

def M86words : List Nat := M86p0

theorem M86wire : module.encode M86 = M86words := by
  rw [module_fast]
  rfl

theorem M86wordBound : M86words.all wordBound = true := by
  simp only [M86words,List.all_append,M86p0bound]
  try rfl

theorem M86bounded : ∀ n ∈ M86words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M86wordBound

end DivRemFV.Replay
