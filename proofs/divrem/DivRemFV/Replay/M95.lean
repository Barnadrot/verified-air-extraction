import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M95 : Module := ⟨95, [36,114,97,110,103,101,95,117,49,51], true, false, [⟨0, [118,97,108,117,101], (some (13)), false, true, false⟩], ((List.range 8192).map (fun n => [n]))⟩

def M95p0 : List Nat := [95,10,36,114,97,110,103,101,95,117,49,51,1,0,0,0,1,0,5,118,97,108,117,101,1,13,0,0,1,0,0,0,8192]
theorem M95p0bound : M95p0.all wordBound = true := (by decide : [95,10,36,114,97,110,103,101,95,117,49,51,1,0,0,0,1,0,5,118,97,108,117,101,1,13,0,0,1,0,0,0,8192].all wordBound = true)

def M95p1 : List Nat := ((List.range' 0 8192).flatMap (fun n => [1,n]))
theorem M95p1bound : M95p1.all wordBound = true := (pairRangeBound 0 8192 (by decide))

def M95words : List Nat := M95p0 ++ M95p1

theorem M95wire : module.encode M95 = M95words := by
  rw [module_fast]
  simp only [M95, M95words,M95p0,M95p1,moduleWords,columnWords,natListWords,boolWords,optionNatWords,List.length_cons,List.length_nil,List.length_map,List.length_range,List.length_range',List.flatMap_cons,List.flatMap_nil,List.flatMap_map,List.nil_append,List.cons_append,List.append_assoc,List.range_eq_range']
  norm_num1
  try rfl

theorem M95wordBound : M95words.all wordBound = true := by
  simp only [M95words,List.all_append,M95p0bound,M95p1bound]
  try rfl

theorem M95bounded : ∀ n ∈ M95words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M95wordBound

end DivRemFV.Replay
