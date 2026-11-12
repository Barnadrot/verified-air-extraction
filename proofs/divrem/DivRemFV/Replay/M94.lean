import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M94 : Module := ⟨94, [36,114,97,110,103,101,95,117,49,50], true, false, [⟨0, [118,97,108,117,101], (some (12)), false, true, false⟩], ((List.range 4096).map (fun n => [n]))⟩

def M94p0 : List Nat := [94,10,36,114,97,110,103,101,95,117,49,50,1,0,0,0,1,0,5,118,97,108,117,101,1,12,0,0,1,0,0,0,4096]
theorem M94p0bound : M94p0.all wordBound = true := (by decide : [94,10,36,114,97,110,103,101,95,117,49,50,1,0,0,0,1,0,5,118,97,108,117,101,1,12,0,0,1,0,0,0,4096].all wordBound = true)

def M94p1 : List Nat := ((List.range' 0 4096).flatMap (fun n => [1,n]))
theorem M94p1bound : M94p1.all wordBound = true := (pairRangeBound 0 4096 (by decide))

def M94words : List Nat := M94p0 ++ M94p1

theorem M94wire : module.encode M94 = M94words := by
  rw [module_fast]
  simp only [M94, M94words,M94p0,M94p1,moduleWords,columnWords,natListWords,boolWords,optionNatWords,List.length_cons,List.length_nil,List.length_map,List.length_range,List.length_range',List.flatMap_cons,List.flatMap_nil,List.flatMap_map,List.nil_append,List.cons_append,List.append_assoc,List.range_eq_range']
  norm_num1
  try rfl

theorem M94wordBound : M94words.all wordBound = true := by
  simp only [M94words,List.all_append,M94p0bound,M94p1bound]
  try rfl

theorem M94bounded : ∀ n ∈ M94words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M94wordBound

end DivRemFV.Replay
