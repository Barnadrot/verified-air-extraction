import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M97 : Module := ⟨97, [36,114,97,110,103,101,95,117,49,53], true, false, [⟨0, [118,97,108,117,101], (some (15)), false, true, false⟩], ((List.range 32768).map (fun n => [n]))⟩

def M97p0 : List Nat := [97,10,36,114,97,110,103,101,95,117,49,53,1,0,0,0,1,0,5,118,97,108,117,101,1,15,0,0,1,0,0,0,32768]
theorem M97p0bound : M97p0.all wordBound = true := (by decide : [97,10,36,114,97,110,103,101,95,117,49,53,1,0,0,0,1,0,5,118,97,108,117,101,1,15,0,0,1,0,0,0,32768].all wordBound = true)

def M97p1 : List Nat := ((List.range' 0 32768).flatMap (fun n => [1,n]))
theorem M97p1bound : M97p1.all wordBound = true := (pairRangeBound 0 32768 (by decide))

def M97words : List Nat := M97p0 ++ M97p1

theorem M97wire : module.encode M97 = M97words := by
  rw [module_fast]
  simp only [M97, M97words,M97p0,M97p1,moduleWords,columnWords,natListWords,boolWords,optionNatWords,List.length_cons,List.length_nil,List.length_map,List.length_range,List.length_range',List.flatMap_cons,List.flatMap_nil,List.flatMap_map,List.nil_append,List.cons_append,List.append_assoc,List.range_eq_range']
  norm_num1
  try rfl

theorem M97wordBound : M97words.all wordBound = true := by
  simp only [M97words,List.all_append,M97p0bound,M97p1bound]
  try rfl

theorem M97bounded : ∀ n ∈ M97words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M97wordBound

end DivRemFV.Replay
