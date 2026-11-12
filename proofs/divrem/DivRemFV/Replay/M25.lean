import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M25 : Module := ⟨25, [105,110,116,101,114,110,97,108,95,100,105,97,103], true, false, [⟨0, [105], (some (5)), true, false, false⟩,⟨1, [68,105], none, false, true, true⟩], [[0,2130706431],[1,1],[2,2],[3,1065353217],[4,3],[5,4],[6,1065353216],[7,2130706430],[8,2130706429],[9,2122383361],[10,1864368129],[11,2130706306],[12,8323072],[13,266338304],[14,133169152],[15,127]]⟩

def M25p0 : List Nat := [25,13,105,110,116,101,114,110,97,108,95,100,105,97,103,1,0,0,0,2,0,1,105,1,5,1,0,0,0,0,0,1,2,68,105,0,0,0,0,1,0,1,0,16,2,0,2130706431,2,1,1,2,2,2,2,3,1065353217,2,4,3,2,5,4,2,6,1065353216,2,7,2130706430,2,8,2130706429,2,9,2122383361,2,10,1864368129,2,11,2130706306,2,12,8323072,2,13,266338304,2,14,133169152,2,15,127]
theorem M25p0bound : M25p0.all wordBound = true := (by decide : [25,13,105,110,116,101,114,110,97,108,95,100,105,97,103,1,0,0,0,2,0,1,105,1,5,1,0,0,0,0,0,1,2,68,105,0,0,0,0,1,0,1,0,16,2,0,2130706431,2,1,1,2,2,2,2,3,1065353217,2,4,3,2,5,4,2,6,1065353216,2,7,2130706430,2,8,2130706429,2,9,2122383361,2,10,1864368129,2,11,2130706306,2,12,8323072,2,13,266338304,2,14,133169152,2,15,127].all wordBound = true)

def M25words : List Nat := M25p0

theorem M25wire : module.encode M25 = M25words := by
  rw [module_fast]
  rfl

theorem M25wordBound : M25words.all wordBound = true := by
  simp only [M25words,List.all_append,M25p0bound]
  try rfl

theorem M25bounded : ∀ n ∈ M25words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M25wordBound

end DivRemFV.Replay
