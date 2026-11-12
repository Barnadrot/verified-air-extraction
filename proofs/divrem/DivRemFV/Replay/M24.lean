import DivRemFV.Replay.R24_0
import DivRemFV.Replay.R24_1
import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M24 : Module := ⟨24, [114,111,117,110,100,95,107,101,121,115], true, false, [⟨0, [105,106], (some (10)), true, false, false⟩,⟨1, [82,105,106], none, false, true, true⟩], R24_0 ++ R24_1⟩

def M24prefix : List Nat := [24,10,114,111,117,110,100,95,107,101,121,115,1,0,0,0,2,0,2,105,106,1,10,1,0,0,0,0,0,1,3,82,105,106,0,0,0,0,1,0,1,0,512]
theorem M24prefixBound : M24prefix.all wordBound = true := by decide

def M24words : List Nat := M24prefix ++ R24_0words ++ R24_1words

theorem M24wire : module.encode M24 = M24words := by
  rw [module_fast]
  simp only [M24,moduleWords,List.length_append,List.flatMap_append,R24_0length,R24_1length,R24_0fast,R24_1fast]
  rfl

theorem M24wordBound : M24words.all wordBound = true := by
  simp only [M24words,List.all_append,M24prefixBound,R24_0wordBound,R24_1wordBound]
  try rfl

theorem M24bounded : ∀ n ∈ M24words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M24wordBound

end DivRemFV.Replay
