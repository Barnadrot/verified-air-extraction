import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M88 : Module := ⟨88, [36,114,97,110,103,101,95,117,54], true, false, [⟨0, [118,97,108,117,101], (some (6)), false, true, false⟩], ((List.range 64).map (fun n => [n]))⟩

def M88p0 : List Nat := [88,9,36,114,97,110,103,101,95,117,54,1,0,0,0,1,0,5,118,97,108,117,101,1,6,0,0,1,0,0,0,64]
theorem M88p0bound : M88p0.all wordBound = true := (by decide : [88,9,36,114,97,110,103,101,95,117,54,1,0,0,0,1,0,5,118,97,108,117,101,1,6,0,0,1,0,0,0,64].all wordBound = true)

def M88p1 : List Nat := ((List.range' 0 64).flatMap (fun n => [1,n]))
theorem M88p1bound : M88p1.all wordBound = true := (pairRangeBound 0 64 (by decide))

def M88words : List Nat := M88p0 ++ M88p1

theorem M88wire : module.encode M88 = M88words := by
  rw [module_fast]
  rfl

theorem M88wordBound : M88words.all wordBound = true := by
  simp only [M88words,List.all_append,M88p0bound,M88p1bound]
  try rfl

theorem M88bounded : ∀ n ∈ M88words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M88wordBound

end DivRemFV.Replay
