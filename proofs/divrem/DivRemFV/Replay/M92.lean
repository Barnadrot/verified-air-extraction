import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M92 : Module := ⟨92, [36,114,97,110,103,101,95,117,49,48], true, false, [⟨0, [118,97,108,117,101], (some (10)), false, true, false⟩], ((List.range 1024).map (fun n => [n]))⟩

def M92p0 : List Nat := [92,10,36,114,97,110,103,101,95,117,49,48,1,0,0,0,1,0,5,118,97,108,117,101,1,10,0,0,1,0,0,0,1024]
theorem M92p0bound : M92p0.all wordBound = true := (by decide : [92,10,36,114,97,110,103,101,95,117,49,48,1,0,0,0,1,0,5,118,97,108,117,101,1,10,0,0,1,0,0,0,1024].all wordBound = true)

def M92p1 : List Nat := ((List.range' 0 1024).flatMap (fun n => [1,n]))
theorem M92p1bound : M92p1.all wordBound = true := (pairRangeBound 0 1024 (by decide))

def M92words : List Nat := M92p0 ++ M92p1

theorem M92wire : module.encode M92 = M92words := by
  rw [module_fast]
  rfl

theorem M92wordBound : M92words.all wordBound = true := by
  simp only [M92words,List.all_append,M92p0bound,M92p1bound]
  try rfl

theorem M92bounded : ∀ n ∈ M92words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M92wordBound

end DivRemFV.Replay
