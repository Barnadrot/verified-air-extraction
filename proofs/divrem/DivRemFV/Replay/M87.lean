import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def M87 : Module := ⟨87, [36,114,97,110,103,101,95,117,53], true, false, [⟨0, [118,97,108,117,101], (some (5)), false, true, false⟩], ((List.range 32).map (fun n => [n]))⟩

def M87p0 : List Nat := [87,9,36,114,97,110,103,101,95,117,53,1,0,0,0,1,0,5,118,97,108,117,101,1,5,0,0,1,0,0,0,32]
theorem M87p0bound : M87p0.all wordBound = true := (by decide : [87,9,36,114,97,110,103,101,95,117,53,1,0,0,0,1,0,5,118,97,108,117,101,1,5,0,0,1,0,0,0,32].all wordBound = true)

def M87p1 : List Nat := ((List.range' 0 32).flatMap (fun n => [1,n]))
theorem M87p1bound : M87p1.all wordBound = true := (pairRangeBound 0 32 (by decide))

def M87words : List Nat := M87p0 ++ M87p1

theorem M87wire : module.encode M87 = M87words := by
  rw [module_fast]
  rfl

theorem M87wordBound : M87words.all wordBound = true := by
  simp only [M87words,List.all_append,M87p0bound,M87p1bound]
  try rfl

theorem M87bounded : ∀ n ∈ M87words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using M87wordBound

end DivRemFV.Replay
