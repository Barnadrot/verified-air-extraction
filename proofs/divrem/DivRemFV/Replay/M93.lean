import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M93 : Module := ⟨93, [36,114,97,110,103,101,95,117,49,49], true, false, [⟨0, [118,97,108,117,101], (some (11)), false, true, false⟩], ((List.range 2048).map (fun n => [n]))⟩

def M93p0 : List Nat := [93,10,36,114,97,110,103,101,95,117,49,49,1,0,0,0,1,0,5,118,97,108,117,101,1,11,0,0,1,0,0,0,2048]
theorem M93p0bound : M93p0.all wordBound = true := (by decide : [93,10,36,114,97,110,103,101,95,117,49,49,1,0,0,0,1,0,5,118,97,108,117,101,1,11,0,0,1,0,0,0,2048].all wordBound = true)

def M93p1 : List Nat := ((List.range' 0 2048).flatMap (fun n => [1,n]))
theorem M93p1bound : M93p1.all wordBound = true := (pairRangeBound 0 2048 (by decide))

def M93words : List Nat := M93p0 ++ M93p1

theorem M93wire : module.encode M93 = M93words := by
  rw [module_fast]
  simp only [M93, M93words,M93p0,M93p1,moduleWords,columnWords,natListWords,boolWords,optionNatWords,List.length_cons,List.length_nil,List.length_map,List.length_range,List.length_range',List.flatMap_cons,List.flatMap_nil,List.flatMap_map,List.nil_append,List.cons_append,List.append_assoc,List.range_eq_range']
  norm_num1
  try rfl

theorem M93wordBound : M93words.all wordBound = true := by
  simp only [M93words,List.all_append,M93p0bound,M93p1bound]
  try rfl

theorem M93bounded : ∀ n ∈ M93words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M93wordBound

end DivRemFV.Replay
