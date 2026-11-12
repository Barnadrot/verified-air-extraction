import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M96 : Module := ⟨96, [36,114,97,110,103,101,95,117,49,52], true, false, [⟨0, [118,97,108,117,101], (some (14)), false, true, false⟩], ((List.range 16384).map (fun n => [n]))⟩

def M96p0 : List Nat := [96,10,36,114,97,110,103,101,95,117,49,52,1,0,0,0,1,0,5,118,97,108,117,101,1,14,0,0,1,0,0,0,16384]
theorem M96p0bound : M96p0.all wordBound = true := (by decide : [96,10,36,114,97,110,103,101,95,117,49,52,1,0,0,0,1,0,5,118,97,108,117,101,1,14,0,0,1,0,0,0,16384].all wordBound = true)

def M96p1 : List Nat := ((List.range' 0 16384).flatMap (fun n => [1,n]))
theorem M96p1bound : M96p1.all wordBound = true := (pairRangeBound 0 16384 (by decide))

def M96words : List Nat := M96p0 ++ M96p1

theorem M96wire : module.encode M96 = M96words := by
  rw [module_fast]
  simp only [M96, M96words,M96p0,M96p1,moduleWords,columnWords,natListWords,boolWords,optionNatWords,List.length_cons,List.length_nil,List.length_map,List.length_range,List.length_range',List.flatMap_cons,List.flatMap_nil,List.flatMap_map,List.nil_append,List.cons_append,List.append_assoc,List.range_eq_range']
  norm_num1
  try rfl

theorem M96wordBound : M96words.all wordBound = true := by
  simp only [M96words,List.all_append,M96p0bound,M96p1bound]
  try rfl

theorem M96bounded : ∀ n ∈ M96words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M96wordBound

end DivRemFV.Replay
