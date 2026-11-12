import DivRemFV.TableCompression
import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M82 : Module := ⟨82, [36,98,105,116,95,120,111,97,95,117,56], true, false, [⟨0, [97], (some (8)), true, false, false⟩,⟨1, [98], (some (8)), true, false, false⟩,⟨2, [97,110,100], (some (8)), false, true, false⟩,⟨3, [111,114], (some (8)), false, true, false⟩,⟨4, [120,111,114], (some (8)), false, true, false⟩], (List.range 65536).map byteTableRow⟩

def M82prefix : List Nat := [82,11,36,98,105,116,95,120,111,97,95,117,56,1,0,0,0,5,0,1,97,1,8,1,0,0,0,0,0,1,1,98,1,8,1,0,0,0,0,0,2,3,97,110,100,1,8,0,0,1,0,0,0,3,2,111,114,1,8,0,0,1,0,0,0,4,3,120,111,114,1,8,0,0,1,0,0,0,65536]
theorem M82prefixwordBound : M82prefix.all wordBound = true := by decide

def M82words : List Nat := M82prefix ++ (List.range 65536).flatMap (fun n => 5 :: byteTableRow n)

theorem M82wire : module.encode M82 = M82words := by
  rw [module_fast]
  simp only [M82,moduleWords,List.length_map,List.length_range,List.flatMap_map,byteTableRow_fast]
  rfl

theorem M82wordBound : M82words.all wordBound = true := by
  simp only [M82words,List.all_append,M82prefixwordBound,byteTable_bounded]
  rfl

theorem M82bounded : ∀ n ∈ M82words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M82wordBound

end DivRemFV.Replay
