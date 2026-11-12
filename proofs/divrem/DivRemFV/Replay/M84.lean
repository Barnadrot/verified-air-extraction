import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M84 : Module := ⟨84, [36,114,97,110,103,101,95,117,50], true, false, [⟨0, [118,97,108,117,101], (some (2)), false, true, false⟩], ((List.range 4).map (fun n => [n]))⟩

def M84p0 : List Nat := [84,9,36,114,97,110,103,101,95,117,50,1,0,0,0,1,0,5,118,97,108,117,101,1,2,0,0,1,0,0,0,4,1,0,1,1,1,2,1,3]
theorem M84p0bound : M84p0.all wordBound = true := (by decide : [84,9,36,114,97,110,103,101,95,117,50,1,0,0,0,1,0,5,118,97,108,117,101,1,2,0,0,1,0,0,0,4,1,0,1,1,1,2,1,3].all wordBound = true)

def M84words : List Nat := M84p0

theorem M84wire : module.encode M84 = M84words := by
  rw [module_fast]
  rfl

theorem M84wordBound : M84words.all wordBound = true := by
  simp only [M84words,List.all_append,M84p0bound]
  try rfl

theorem M84bounded : ∀ n ∈ M84words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M84wordBound

end DivRemFV.Replay
