import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M69 : Module := ⟨69, [115,103,110,95,101,120,116,101,110,115,105,111,110,95,117,56,95,117,54,52], false, false, [⟨0, [118,97,108,117,101], (some (8)), true, false, false⟩,⟨1, [101,120,116,95,118,97,108,117,101,39,51], (some (16)), false, true, false⟩,⟨2, [101,120,116,95,118,97,108,117,101,39,50], (some (16)), false, true, false⟩,⟨3, [101,120,116,95,118,97,108,117,101,39,49], (some (16)), false, true, false⟩,⟨4, [101,120,116,95,118,97,108,117,101,39,48], (some (16)), false, true, false⟩,⟨5, [115,105,103,110], (some (1)), false, false, false⟩,⟨6, [116,109,112], (some (7)), false, false, false⟩,⟨7, [36,114,101,116], (some (1)), false, false, false⟩], ((List.range 0).map (fun n => [n]))⟩

def M69p0 : List Nat := [69,20,115,103,110,95,101,120,116,101,110,115,105,111,110,95,117,56,95,117,54,52,0,0,0,0,8,0,5,118,97,108,117,101,1,8,1,0,0,0,0,0,1,11,101,120,116,95,118,97,108,117,101,39,51,1,16,0,0,1,0,0,0,2,11,101,120,116,95,118,97,108,117,101,39,50,1,16,0,0,1,0,0,0,3,11,101,120,116,95,118,97,108,117,101,39,49,1,16,0,0,1,0,0,0,4,11,101,120,116,95,118,97,108,117,101,39,48,1,16,0,0,1,0,0,0,5,4]
theorem M69p0bound : M69p0.all wordBound = true := (by decide : [69,20,115,103,110,95,101,120,116,101,110,115,105,111,110,95,117,56,95,117,54,52,0,0,0,0,8,0,5,118,97,108,117,101,1,8,1,0,0,0,0,0,1,11,101,120,116,95,118,97,108,117,101,39,51,1,16,0,0,1,0,0,0,2,11,101,120,116,95,118,97,108,117,101,39,50,1,16,0,0,1,0,0,0,3,11,101,120,116,95,118,97,108,117,101,39,49,1,16,0,0,1,0,0,0,4,11,101,120,116,95,118,97,108,117,101,39,48,1,16,0,0,1,0,0,0,5,4].all wordBound = true)

def M69p1 : List Nat := [115,105,103,110,1,1,0,0,0,0,0,0,6,3,116,109,112,1,7,0,0,0,0,0,0,7,4,36,114,101,116,1,1,0,0,0,0,0,0,0]
theorem M69p1bound : M69p1.all wordBound = true := (by decide : [115,105,103,110,1,1,0,0,0,0,0,0,6,3,116,109,112,1,7,0,0,0,0,0,0,7,4,36,114,101,116,1,1,0,0,0,0,0,0,0].all wordBound = true)

def M69words : List Nat := M69p0 ++ M69p1

theorem M69wire : module.encode M69 = M69words := by
  rw [module_fast]
  rfl

theorem M69wordBound : M69words.all wordBound = true := by
  simp only [M69words,List.all_append,M69p0bound,M69p1bound]
  try rfl

theorem M69bounded : ∀ n ∈ M69words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M69wordBound

end DivRemFV.Replay
