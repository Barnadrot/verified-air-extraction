import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M68 : Module := ⟨68, [115,103,110,95,101,120,116,101,110,115,105,111,110,95,117,49,54,95,117,54,52], false, false, [⟨0, [118,97,108,117,101], (some (16)), true, false, false⟩,⟨1, [101,120,116,95,118,97,108,117,101,39,51], (some (16)), false, true, false⟩,⟨2, [101,120,116,95,118,97,108,117,101,39,50], (some (16)), false, true, false⟩,⟨3, [101,120,116,95,118,97,108,117,101,39,49], (some (16)), false, true, false⟩,⟨4, [101,120,116,95,118,97,108,117,101,39,48], (some (16)), false, true, false⟩,⟨5, [115,105,103,110], (some (1)), false, false, false⟩,⟨6, [116,109,112], (some (15)), false, false, false⟩,⟨7, [36,114,101,116], (some (1)), false, false, false⟩], ((List.range 0).map (fun n => [n]))⟩

def M68p0 : List Nat := [68,21,115,103,110,95,101,120,116,101,110,115,105,111,110,95,117,49,54,95,117,54,52,0,0,0,0,8,0,5,118,97,108,117,101,1,16,1,0,0,0,0,0,1,11,101,120,116,95,118,97,108,117,101,39,51,1,16,0,0,1,0,0,0,2,11,101,120,116,95,118,97,108,117,101,39,50,1,16,0,0,1,0,0,0,3,11,101,120,116,95,118,97,108,117,101,39,49,1,16,0,0,1,0,0,0,4,11,101,120,116,95,118,97,108,117,101,39,48,1,16,0,0,1,0,0,0,5]
theorem M68p0bound : M68p0.all wordBound = true := (by decide : [68,21,115,103,110,95,101,120,116,101,110,115,105,111,110,95,117,49,54,95,117,54,52,0,0,0,0,8,0,5,118,97,108,117,101,1,16,1,0,0,0,0,0,1,11,101,120,116,95,118,97,108,117,101,39,51,1,16,0,0,1,0,0,0,2,11,101,120,116,95,118,97,108,117,101,39,50,1,16,0,0,1,0,0,0,3,11,101,120,116,95,118,97,108,117,101,39,49,1,16,0,0,1,0,0,0,4,11,101,120,116,95,118,97,108,117,101,39,48,1,16,0,0,1,0,0,0,5].all wordBound = true)

def M68p1 : List Nat := [4,115,105,103,110,1,1,0,0,0,0,0,0,6,3,116,109,112,1,15,0,0,0,0,0,0,7,4,36,114,101,116,1,1,0,0,0,0,0,0,0]
theorem M68p1bound : M68p1.all wordBound = true := (by decide : [4,115,105,103,110,1,1,0,0,0,0,0,0,6,3,116,109,112,1,15,0,0,0,0,0,0,7,4,36,114,101,116,1,1,0,0,0,0,0,0,0].all wordBound = true)

def M68words : List Nat := M68p0 ++ M68p1

theorem M68wire : module.encode M68 = M68words := by
  rw [module_fast]
  rfl

theorem M68wordBound : M68words.all wordBound = true := by
  simp only [M68words,List.all_append,M68p0bound,M68p1bound]
  try rfl

theorem M68bounded : ∀ n ∈ M68words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M68wordBound

end DivRemFV.Replay
