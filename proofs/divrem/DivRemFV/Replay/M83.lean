import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C83_0 : List Column := [⟨0, [97,114,103,49], (some (16)), true, false, false⟩,⟨1, [97,114,103,50], (some (16)), true, false, false⟩,⟨2, [97,110,100], (some (16)), false, true, false⟩,⟨3, [111,114], (some (16)), false, true, false⟩,⟨4, [120,111,114], (some (16)), false, true, false⟩,⟨5, [97,114,103,95,49,95,108,111,95,36,48], (some (8)), false, false, false⟩,⟨6, [97,114,103,95,49,95,104,105,95,36,49], (some (8)), false, false, false⟩,⟨7, [97,114,103,95,50,95,108,111,95,36,50], (some (8)), false, false, false⟩]

def C83_0p0 : List Nat := [0,4,97,114,103,49,1,16,1,0,0,0,0,0,1,4,97,114,103,50,1,16,1,0,0,0,0,0,2,3,97,110,100,1,16,0,0,1,0,0,0,3,2,111,114,1,16,0,0,1,0,0,0,4,3,120,111,114,1,16,0,0,1,0,0,0,5,11,97,114,103,95,49,95,108,111,95,36,48,1,8,0,0,0,0,0,0,6,11,97,114,103,95,49,95,104,105,95,36,49,1,8,0,0,0,0,0,0,7,11,97,114,103,95,50,95,108,111,95,36,50,1,8,0,0,0,0,0]
theorem C83_0p0bound : C83_0p0.all wordBound = true := (by decide : [0,4,97,114,103,49,1,16,1,0,0,0,0,0,1,4,97,114,103,50,1,16,1,0,0,0,0,0,2,3,97,110,100,1,16,0,0,1,0,0,0,3,2,111,114,1,16,0,0,1,0,0,0,4,3,120,111,114,1,16,0,0,1,0,0,0,5,11,97,114,103,95,49,95,108,111,95,36,48,1,8,0,0,0,0,0,0,6,11,97,114,103,95,49,95,104,105,95,36,49,1,8,0,0,0,0,0,0,7,11,97,114,103,95,50,95,108,111,95,36,50,1,8,0,0,0,0,0].all wordBound = true)

def C83_0p1 : List Nat := [0]
theorem C83_0p1bound : C83_0p1.all wordBound = true := (by decide : [0].all wordBound = true)

def C83_0words : List Nat := C83_0p0 ++ C83_0p1

theorem C83_0wire : C83_0.flatMap columnWords = C83_0words := by
  rfl

theorem C83_0wordBound : C83_0words.all wordBound = true := by
  simp only [C83_0words,List.all_append,C83_0p0bound,C83_0p1bound]
  try rfl

theorem C83_0bounded : ∀ n ∈ C83_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C83_0wordBound

theorem C83_0length : C83_0.length = 8 := by rfl

def C83_1 : List Column := [⟨8, [97,114,103,95,50,95,104,105,95,36,51], (some (8)), false, false, false⟩,⟨9, [114,101,115,76,111,119,95,65,78,68,95,36,52], (some (8)), false, false, false⟩,⟨10, [114,101,115,72,105,103,104,95,65,78,68,95,36,53], (some (8)), false, false, false⟩,⟨11, [114,101,115,76,111,119,95,79,82,95,36,54], (some (8)), false, false, false⟩,⟨12, [114,101,115,72,105,103,104,95,79,82,95,36,55], (some (8)), false, false, false⟩,⟨13, [114,101,115,76,111,119,95,88,79,82,95,36,56], (some (8)), false, false, false⟩,⟨14, [114,101,115,72,105,103,104,95,88,79,82,95,36,57], (some (8)), false, false, false⟩,⟨15, [36,114,101,116], (some (1)), false, false, false⟩]

def C83_1p0 : List Nat := [8,11,97,114,103,95,50,95,104,105,95,36,51,1,8,0,0,0,0,0,0,9,13,114,101,115,76,111,119,95,65,78,68,95,36,52,1,8,0,0,0,0,0,0,10,14,114,101,115,72,105,103,104,95,65,78,68,95,36,53,1,8,0,0,0,0,0,0,11,12,114,101,115,76,111,119,95,79,82,95,36,54,1,8,0,0,0,0,0,0,12,13,114,101,115,72,105,103,104,95,79,82,95,36,55,1,8,0,0,0,0,0,0,13,13,114,101,115,76,111,119,95,88,79,82,95,36,56]
theorem C83_1p0bound : C83_1p0.all wordBound = true := (by decide : [8,11,97,114,103,95,50,95,104,105,95,36,51,1,8,0,0,0,0,0,0,9,13,114,101,115,76,111,119,95,65,78,68,95,36,52,1,8,0,0,0,0,0,0,10,14,114,101,115,72,105,103,104,95,65,78,68,95,36,53,1,8,0,0,0,0,0,0,11,12,114,101,115,76,111,119,95,79,82,95,36,54,1,8,0,0,0,0,0,0,12,13,114,101,115,72,105,103,104,95,79,82,95,36,55,1,8,0,0,0,0,0,0,13,13,114,101,115,76,111,119,95,88,79,82,95,36,56].all wordBound = true)

def C83_1p1 : List Nat := [1,8,0,0,0,0,0,0,14,14,114,101,115,72,105,103,104,95,88,79,82,95,36,57,1,8,0,0,0,0,0,0,15,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C83_1p1bound : C83_1p1.all wordBound = true := (by decide : [1,8,0,0,0,0,0,0,14,14,114,101,115,72,105,103,104,95,88,79,82,95,36,57,1,8,0,0,0,0,0,0,15,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C83_1words : List Nat := C83_1p0 ++ C83_1p1

theorem C83_1wire : C83_1.flatMap columnWords = C83_1words := by
  rfl

theorem C83_1wordBound : C83_1words.all wordBound = true := by
  simp only [C83_1words,List.all_append,C83_1p0bound,C83_1p1bound]
  try rfl

theorem C83_1bounded : ∀ n ∈ C83_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C83_1wordBound

theorem C83_1length : C83_1.length = 8 := by rfl

def M83 : Module := ⟨83, [36,98,105,116,95,120,111,97,95,117,49,54], false, false, C83_0 ++ C83_1, ((List.range 0).map (fun n => [n]))⟩

def M83prefix : List Nat := [83,12,36,98,105,116,95,120,111,97,95,117,49,54,0,0,0,0,16]
theorem M83prefixwordBound : M83prefix.all wordBound = true := by decide

def M83words : List Nat := M83prefix ++ C83_0words ++ C83_1words ++ [0]

theorem M83wire : module.encode M83 = M83words := by
  rw [module_fast]
  simp only [M83,moduleWords,List.length_append,List.flatMap_append,C83_0length,C83_1length,C83_0wire,C83_1wire]
  rfl

theorem M83wordBound : M83words.all wordBound = true := by
  simp only [M83words,List.all_append,M83prefixwordBound,C83_0wordBound,C83_1wordBound]
  decide

theorem M83bounded : ∀ n ∈ M83words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M83wordBound

end DivRemFV.Replay
