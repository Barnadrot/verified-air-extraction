import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M3 : Module := ⟨3, [105,110,115,116,114,117,99,116,105,111,110,95,98,97,115,101], false, false, [⟨0, [105], (some (1)), true, false, false⟩,⟨1, [98,97,115,101,39,51], (some (16)), false, true, false⟩,⟨2, [98,97,115,101,39,50], (some (16)), false, true, false⟩,⟨3, [98,97,115,101,39,49], (some (16)), false, true, false⟩,⟨4, [98,97,115,101,39,48], (some (16)), false, true, false⟩,⟨5, [36,97,99,99,101,115,115,95,98,105,116], (some (1)), false, false, false⟩], ((List.range 0).map (fun n => [n]))⟩

def M3p0 : List Nat := [3,16,105,110,115,116,114,117,99,116,105,111,110,95,98,97,115,101,0,0,0,0,6,0,1,105,1,1,1,0,0,0,0,0,1,6,98,97,115,101,39,51,1,16,0,0,1,0,0,0,2,6,98,97,115,101,39,50,1,16,0,0,1,0,0,0,3,6,98,97,115,101,39,49,1,16,0,0,1,0,0,0,4,6,98,97,115,101,39,48,1,16,0,0,1,0,0,0,5,11,36,97,99,99,101,115,115,95,98,105,116,1,1,0,0,0,0,0,0,0]
theorem M3p0bound : M3p0.all wordBound = true := (by decide : [3,16,105,110,115,116,114,117,99,116,105,111,110,95,98,97,115,101,0,0,0,0,6,0,1,105,1,1,1,0,0,0,0,0,1,6,98,97,115,101,39,51,1,16,0,0,1,0,0,0,2,6,98,97,115,101,39,50,1,16,0,0,1,0,0,0,3,6,98,97,115,101,39,49,1,16,0,0,1,0,0,0,4,6,98,97,115,101,39,48,1,16,0,0,1,0,0,0,5,11,36,97,99,99,101,115,115,95,98,105,116,1,1,0,0,0,0,0,0,0].all wordBound = true)

def M3words : List Nat := M3p0

theorem M3wire : module.encode M3 = M3words := by
  rw [module_fast]
  rfl

theorem M3wordBound : M3words.all wordBound = true := by
  simp only [M3words,List.all_append,M3p0bound]
  try rfl

theorem M3bounded : ∀ n ∈ M3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M3wordBound

end DivRemFV.Replay
