import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M29 : Module := ⟨29, [115,98,111,120], false, false, [⟨0, [120], none, true, false, true⟩,⟨1, [114,101,115], none, false, true, true⟩,⟨2, [36,50], none, false, false, true⟩,⟨3, [36,114,101,116], (some (1)), false, false, false⟩], ((List.range 0).map (fun n => [n]))⟩

def M29p0 : List Nat := [29,4,115,98,111,120,0,0,0,0,4,0,1,120,0,0,1,0,0,0,1,0,1,3,114,101,115,0,0,0,0,1,0,1,0,2,2,36,50,0,0,0,0,0,0,1,0,3,4,36,114,101,116,1,1,0,0,0,0,0,0,0]
theorem M29p0bound : M29p0.all wordBound = true := (by decide : [29,4,115,98,111,120,0,0,0,0,4,0,1,120,0,0,1,0,0,0,1,0,1,3,114,101,115,0,0,0,0,1,0,1,0,2,2,36,50,0,0,0,0,0,0,1,0,3,4,36,114,101,116,1,1,0,0,0,0,0,0,0].all wordBound = true)

def M29words : List Nat := M29p0

theorem M29wire : module.encode M29 = M29words := by
  rw [module_fast]
  rfl

theorem M29wordBound : M29words.all wordBound = true := by
  simp only [M29words,List.all_append,M29p0bound]
  try rfl

theorem M29bounded : ∀ n ∈ M29words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M29wordBound

end DivRemFV.Replay
