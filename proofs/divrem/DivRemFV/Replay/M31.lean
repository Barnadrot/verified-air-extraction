import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C31_0 : List Column := [⟨0, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [114], (some (5)), true, false, false⟩,⟨3, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨4, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨5, [36,49], (some (5)), false, false, false⟩,⟨6, [36,50], none, false, false, true⟩,⟨7, [36,51], none, false, false, true⟩]

def C31_0p0 : List Nat := [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,1,114,1,5,1,0,0,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,4,27,112,111,115,101,105,100,111,110,50,95,115,116]
theorem C31_0p0bound : C31_0p0.all wordBound = true := (by decide : [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,1,114,1,5,1,0,0,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,4,27,112,111,115,101,105,100,111,110,50,95,115,116].all wordBound = true)

def C31_0p1 : List Nat := [97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,5,2,36,49,1,5,0,0,0,0,0,0,6,2,36,50,0,0,0,0,0,0,1,0,7,2,36,51,0,0,0,0,0,0,1,0]
theorem C31_0p1bound : C31_0p1.all wordBound = true := (by decide : [97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,5,2,36,49,1,5,0,0,0,0,0,0,6,2,36,50,0,0,0,0,0,0,1,0,7,2,36,51,0,0,0,0,0,0,1,0].all wordBound = true)

def C31_0words : List Nat := C31_0p0 ++ C31_0p1

theorem C31_0wire : C31_0.flatMap columnWords = C31_0words := by
  rfl

theorem C31_0wordBound : C31_0words.all wordBound = true := by
  simp only [C31_0words,List.all_append,C31_0p0bound,C31_0p1bound]
  try rfl

theorem C31_0bounded : ∀ n ∈ C31_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C31_0wordBound

theorem C31_0length : C31_0.length = 8 := by rfl

def C31_1 : List Column := [⟨8, [36,52], (some (5)), false, false, false⟩,⟨9, [115,116,97,109,112,36,55,39,49], (some (16)), false, false, false⟩,⟨10, [115,116,97,109,112,36,55,39,48], (some (16)), false, false, false⟩,⟨11, [115,116,97,109,112,36,56,39,49], (some (16)), false, false, false⟩,⟨12, [115,116,97,109,112,36,56,39,48], (some (16)), false, false, false⟩,⟨13, [115,116,97,109,112,36,57,39,49], (some (16)), false, false, false⟩,⟨14, [115,116,97,109,112,36,57,39,48], (some (16)), false, false, false⟩,⟨15, [115,116,97,109,112,36,49,48,39,49], (some (16)), false, false, false⟩]

def C31_1p0 : List Nat := [8,2,36,52,1,5,0,0,0,0,0,0,9,9,115,116,97,109,112,36,55,39,49,1,16,0,0,0,0,0,0,10,9,115,116,97,109,112,36,55,39,48,1,16,0,0,0,0,0,0,11,9,115,116,97,109,112,36,56,39,49,1,16,0,0,0,0,0,0,12,9,115,116,97,109,112,36,56,39,48,1,16,0,0,0,0,0,0,13,9,115,116,97,109,112,36,57,39,49,1,16,0,0,0,0,0,0,14,9,115,116,97,109,112,36,57,39,48,1,16,0,0,0,0,0,0,15,10]
theorem C31_1p0bound : C31_1p0.all wordBound = true := (by decide : [8,2,36,52,1,5,0,0,0,0,0,0,9,9,115,116,97,109,112,36,55,39,49,1,16,0,0,0,0,0,0,10,9,115,116,97,109,112,36,55,39,48,1,16,0,0,0,0,0,0,11,9,115,116,97,109,112,36,56,39,49,1,16,0,0,0,0,0,0,12,9,115,116,97,109,112,36,56,39,48,1,16,0,0,0,0,0,0,13,9,115,116,97,109,112,36,57,39,49,1,16,0,0,0,0,0,0,14,9,115,116,97,109,112,36,57,39,48,1,16,0,0,0,0,0,0,15,10].all wordBound = true)

def C31_1p1 : List Nat := [115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0]
theorem C31_1p1bound : C31_1p1.all wordBound = true := (by decide : [115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C31_1words : List Nat := C31_1p0 ++ C31_1p1

theorem C31_1wire : C31_1.flatMap columnWords = C31_1words := by
  rfl

theorem C31_1wordBound : C31_1words.all wordBound = true := by
  simp only [C31_1words,List.all_append,C31_1p0bound,C31_1p1bound]
  try rfl

theorem C31_1bounded : ∀ n ∈ C31_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C31_1wordBound

theorem C31_1length : C31_1.length = 8 := by rfl

def C31_2 : List Column := [⟨16, [115,116,97,109,112,36,49,48,39,48], (some (16)), false, false, false⟩,⟨17, [99,36,49,55], (some (1)), false, false, false⟩,⟨18, [99,36,49,56], (some (1)), false, false, false⟩,⟨19, [36,114,101,116], (some (1)), false, false, false⟩]

def C31_2p0 : List Nat := [16,10,115,116,97,109,112,36,49,48,39,48,1,16,0,0,0,0,0,0,17,4,99,36,49,55,1,1,0,0,0,0,0,0,18,4,99,36,49,56,1,1,0,0,0,0,0,0,19,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C31_2p0bound : C31_2p0.all wordBound = true := (by decide : [16,10,115,116,97,109,112,36,49,48,39,48,1,16,0,0,0,0,0,0,17,4,99,36,49,55,1,1,0,0,0,0,0,0,18,4,99,36,49,56,1,1,0,0,0,0,0,0,19,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C31_2words : List Nat := C31_2p0

theorem C31_2wire : C31_2.flatMap columnWords = C31_2words := by
  rfl

theorem C31_2wordBound : C31_2words.all wordBound = true := by
  simp only [C31_2words,List.all_append,C31_2p0bound]
  try rfl

theorem C31_2bounded : ∀ n ∈ C31_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C31_2wordBound

theorem C31_2length : C31_2.length = 4 := by rfl

def M31 : Module := ⟨31, [112,97,114,116,105,97,108,95,114,111,117,110,100], false, false, C31_0 ++ C31_1 ++ C31_2, ((List.range 0).map (fun n => [n]))⟩

def M31prefix : List Nat := [31,13,112,97,114,116,105,97,108,95,114,111,117,110,100,0,0,0,0,20]
theorem M31prefixwordBound : M31prefix.all wordBound = true := by decide

def M31words : List Nat := M31prefix ++ C31_0words ++ C31_1words ++ C31_2words ++ [0]

theorem M31wire : module.encode M31 = M31words := by
  rw [module_fast]
  simp only [M31,moduleWords,List.length_append,List.flatMap_append,C31_0length,C31_1length,C31_2length,C31_0wire,C31_1wire,C31_2wire]
  rfl

theorem M31wordBound : M31words.all wordBound = true := by
  simp only [M31words,List.all_append,M31prefixwordBound,C31_0wordBound,C31_1wordBound,C31_2wordBound]
  decide

theorem M31bounded : ∀ n ∈ M31words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M31wordBound

end DivRemFV.Replay
