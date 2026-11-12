import DivRemFV.Replay.FullData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

theorem findM55 : full.modules.find? (fun m => decide (m.id = 55)) = some M55 := by rfl
theorem findM56 : full.modules.find? (fun m => decide (m.id = 56)) = some M56 := by rfl
theorem findM61 : full.modules.find? (fun m => decide (m.id = 61)) = some M61 := by rfl
theorem findM62 : full.modules.find? (fun m => decide (m.id = 62)) = some M62 := by rfl
theorem findM63 : full.modules.find? (fun m => decide (m.id = 63)) = some M63 := by rfl
theorem findM64 : full.modules.find? (fun m => decide (m.id = 64)) = some M64 := by rfl
theorem findM65 : full.modules.find? (fun m => decide (m.id = 65)) = some M65 := by rfl
theorem findM66 : full.modules.find? (fun m => decide (m.id = 66)) = some M66 := by rfl
theorem findM84 : full.modules.find? (fun m => decide (m.id = 84)) = some M84 := by rfl
theorem findM85 : full.modules.find? (fun m => decide (m.id = 85)) = some M85 := by rfl
theorem findM86 : full.modules.find? (fun m => decide (m.id = 86)) = some M86 := by rfl
theorem findM90 : full.modules.find? (fun m => decide (m.id = 90)) = some M90 := by rfl
theorem findM94 : full.modules.find? (fun m => decide (m.id = 94)) = some M94 := by rfl
theorem findM95 : full.modules.find? (fun m => decide (m.id = 95)) = some M95 := by rfl
theorem findM96 : full.modules.find? (fun m => decide (m.id = 96)) = some M96 := by rfl
theorem findM97 : full.modules.find? (fun m => decide (m.id = 97)) = some M97 := by rfl
theorem findM98 : full.modules.find? (fun m => decide (m.id = 98)) = some M98 := by rfl

theorem ranges_checked : ArtifactBinding.rangeCheck full = true := by
  simp (maxSteps := 1000000) only [ArtifactBinding.rangeCheck,rangeTablePairs,List.all_cons,List.all_nil,findM84,findM85,findM86,findM90,findM94,findM95,findM96,findM97,findM98,Bool.and_eq_true,decide_eq_true_eq]
  repeat' first | apply And.intro | rfl | trivial

theorem index_checked : ArtifactBinding.indexCheck full = true := by decide

theorem dynamic_checked : ArtifactBinding.dynamicCheck full = true := by decide

end DivRemFV.Replay
