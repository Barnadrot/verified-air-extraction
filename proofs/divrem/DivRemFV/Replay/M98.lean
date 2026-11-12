import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M98 : Module := ⟨98, [36,114,97,110,103,101,95,117,49,54], true, false, [⟨0, [118,97,108,117,101], (some (16)), false, true, false⟩], ((List.range 65536).map (fun n => [n]))⟩

def M98p0 : List Nat := [98,10,36,114,97,110,103,101,95,117,49,54,1,0,0,0,1,0,5,118,97,108,117,101,1,16,0,0,1,0,0,0,65536]
theorem M98p0bound : M98p0.all wordBound = true := (by decide : [98,10,36,114,97,110,103,101,95,117,49,54,1,0,0,0,1,0,5,118,97,108,117,101,1,16,0,0,1,0,0,0,65536].all wordBound = true)

def M98p1 : List Nat := ((List.range' 0 65536).flatMap (fun n => [1,n]))
theorem M98p1bound : M98p1.all wordBound = true := (pairRangeBound 0 65536 (by decide))

def M98words : List Nat := M98p0 ++ M98p1

theorem M98wire : module.encode M98 = M98words := by
  rw [module_fast]
  simp only [M98, M98words,M98p0,M98p1,moduleWords,columnWords,natListWords,boolWords,optionNatWords,List.length_cons,List.length_nil,List.length_map,List.length_range,List.length_range',List.flatMap_cons,List.flatMap_nil,List.flatMap_map,List.nil_append,List.cons_append,List.append_assoc,List.range_eq_range']
  norm_num1
  try rfl

theorem M98wordBound : M98words.all wordBound = true := by
  simp only [M98words,List.all_append,M98p0bound,M98p1bound]
  try rfl

theorem M98bounded : ∀ n ∈ M98words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M98wordBound

end DivRemFV.Replay
