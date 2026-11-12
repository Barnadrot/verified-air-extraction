import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M74 : Module := ⟨74, [36,102,105,101,108,100,95,114,97,110,103,101,95,117,51,50], false, false, [⟨0, [97,114,103,48,39,49], (some (16)), true, false, false⟩,⟨1, [97,114,103,48,39,48], (some (16)), true, false, false⟩,⟨2, [108,99,109,36,49,39,49], (some (16)), false, false, false⟩,⟨3, [108,99,109,36,49,39,48], (some (16)), false, false, false⟩,⟨4, [108,99,109,36,50], (some (1)), false, false, false⟩,⟨5, [98,36,53], (some (1)), false, false, false⟩,⟨6, [98,36,54], (some (1)), false, false, false⟩,⟨7, [36,114,101,116], (some (1)), false, false, false⟩], ((List.range 0).map (fun n => [n]))⟩

def M74p0 : List Nat := [74,16,36,102,105,101,108,100,95,114,97,110,103,101,95,117,51,50,0,0,0,0,8,0,6,97,114,103,48,39,49,1,16,1,0,0,0,0,0,1,6,97,114,103,48,39,48,1,16,1,0,0,0,0,0,2,7,108,99,109,36,49,39,49,1,16,0,0,0,0,0,0,3,7,108,99,109,36,49,39,48,1,16,0,0,0,0,0,0,4,5,108,99,109,36,50,1,1,0,0,0,0,0,0,5,3,98,36,53,1,1,0,0,0,0,0,0,6,3,98,36,54,1,1,0,0,0,0]
theorem M74p0bound : M74p0.all wordBound = true := (by decide : [74,16,36,102,105,101,108,100,95,114,97,110,103,101,95,117,51,50,0,0,0,0,8,0,6,97,114,103,48,39,49,1,16,1,0,0,0,0,0,1,6,97,114,103,48,39,48,1,16,1,0,0,0,0,0,2,7,108,99,109,36,49,39,49,1,16,0,0,0,0,0,0,3,7,108,99,109,36,49,39,48,1,16,0,0,0,0,0,0,4,5,108,99,109,36,50,1,1,0,0,0,0,0,0,5,3,98,36,53,1,1,0,0,0,0,0,0,6,3,98,36,54,1,1,0,0,0,0].all wordBound = true)

def M74p1 : List Nat := [0,0,7,4,36,114,101,116,1,1,0,0,0,0,0,0,0]
theorem M74p1bound : M74p1.all wordBound = true := (by decide : [0,0,7,4,36,114,101,116,1,1,0,0,0,0,0,0,0].all wordBound = true)

def M74words : List Nat := M74p0 ++ M74p1

theorem M74wire : module.encode M74 = M74words := by
  rw [module_fast]
  rfl

theorem M74wordBound : M74words.all wordBound = true := by
  simp only [M74words,List.all_append,M74p0bound,M74p1bound]
  try rfl

theorem M74bounded : ∀ n ∈ M74words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M74wordBound

end DivRemFV.Replay
