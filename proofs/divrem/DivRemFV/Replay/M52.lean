import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C52_0 : List Column := [⟨0, [114,97,109,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨1, [114,97,109,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨2, [114,97,109,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨3, [97,100,100,114,101,115,115,39,51], (some (16)), true, false, false⟩,⟨4, [97,100,100,114,101,115,115,39,50], (some (16)), true, false, false⟩,⟨5, [97,100,100,114,101,115,115,39,49], (some (16)), true, false, false⟩,⟨6, [97,100,100,114,101,115,115,39,48], (some (16)), true, false, false⟩,⟨7, [118,97,108,117,101], (some (16)), true, false, false⟩]

def C52_0p0 : List Nat := [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115]
theorem C52_0p0bound : C52_0p0.all wordBound = true := (by decide : [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115].all wordBound = true)

def C52_0p1 : List Nat := [115,39,48,1,16,1,0,0,0,0,0,7,5,118,97,108,117,101,1,16,1,0,0,0,0,0]
theorem C52_0p1bound : C52_0p1.all wordBound = true := (by decide : [115,39,48,1,16,1,0,0,0,0,0,7,5,118,97,108,117,101,1,16,1,0,0,0,0,0].all wordBound = true)

def C52_0words : List Nat := C52_0p0 ++ C52_0p1

theorem C52_0wire : C52_0.flatMap columnWords = C52_0words := by
  rfl

theorem C52_0wordBound : C52_0words.all wordBound = true := by
  simp only [C52_0words,List.all_append,C52_0p0bound,C52_0p1bound]
  try rfl

theorem C52_0bounded : ∀ n ∈ C52_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C52_0wordBound

theorem C52_0length : C52_0.length = 8 := by rfl

def C52_1 : List Column := [⟨8, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,50], (some (16)), false, true, false⟩,⟨9, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨10, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨11, [98,111,102,102,115,101,116], (some (2)), false, false, false⟩,⟨12, [119,111,102,102,115,101,116,39,51], (some (14)), false, false, false⟩,⟨13, [119,111,102,102,115,101,116,39,50], (some (16)), false, false, false⟩,⟨14, [119,111,102,102,115,101,116,39,49], (some (16)), false, false, false⟩,⟨15, [119,111,102,102,115,101,116,39,48], (some (16)), false, false, false⟩]

def C52_1p0 : List Nat := [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,10,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,11,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,12,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0]
theorem C52_1p0bound : C52_1p0.all wordBound = true := (by decide : [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,10,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,11,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,12,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0].all wordBound = true)

def C52_1p1 : List Nat := [0,0,14,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0]
theorem C52_1p1bound : C52_1p1.all wordBound = true := (by decide : [0,0,14,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C52_1words : List Nat := C52_1p0 ++ C52_1p1

theorem C52_1wire : C52_1.flatMap columnWords = C52_1words := by
  rfl

theorem C52_1wordBound : C52_1words.all wordBound = true := by
  simp only [C52_1words,List.all_append,C52_1p0bound,C52_1p1bound]
  try rfl

theorem C52_1bounded : ∀ n ∈ C52_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C52_1wordBound

theorem C52_1length : C52_1.length = 8 := by rfl

def C52_2 : List Column := [⟨16, [104,105], (some (16)), false, false, false⟩,⟨17, [108,111], (some (16)), false, false, false⟩,⟨18, [98,48], (some (8)), false, false, false⟩,⟨19, [98,49], (some (8)), false, false, false⟩,⟨20, [36,56,39,49], (some (16)), false, false, false⟩,⟨21, [36,56,39,48], (some (16)), false, false, false⟩,⟨22, [36,57,39,49], (some (16)), false, false, false⟩,⟨23, [36,57,39,48], (some (16)), false, false, false⟩]

def C52_2p0 : List Nat := [16,2,104,105,1,16,0,0,0,0,0,0,17,2,108,111,1,16,0,0,0,0,0,0,18,2,98,48,1,8,0,0,0,0,0,0,19,2,98,49,1,8,0,0,0,0,0,0,20,4,36,56,39,49,1,16,0,0,0,0,0,0,21,4,36,56,39,48,1,16,0,0,0,0,0,0,22,4,36,57,39,49,1,16,0,0,0,0,0,0,23,4,36,57,39,48,1,16,0,0,0,0,0,0]
theorem C52_2p0bound : C52_2p0.all wordBound = true := (by decide : [16,2,104,105,1,16,0,0,0,0,0,0,17,2,108,111,1,16,0,0,0,0,0,0,18,2,98,48,1,8,0,0,0,0,0,0,19,2,98,49,1,8,0,0,0,0,0,0,20,4,36,56,39,49,1,16,0,0,0,0,0,0,21,4,36,56,39,48,1,16,0,0,0,0,0,0,22,4,36,57,39,49,1,16,0,0,0,0,0,0,23,4,36,57,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C52_2words : List Nat := C52_2p0

theorem C52_2wire : C52_2.flatMap columnWords = C52_2words := by
  rfl

theorem C52_2wordBound : C52_2words.all wordBound = true := by
  simp only [C52_2words,List.all_append,C52_2p0bound]
  try rfl

theorem C52_2bounded : ∀ n ∈ C52_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C52_2wordBound

theorem C52_2length : C52_2.length = 8 := by rfl

def C52_3 : List Column := [⟨24, [115,116,97,109,112,36,49,53,39,48], (some (16)), false, false, false⟩,⟨25, [115,116,97,109,112,36,49,54,39,50], (some (16)), false, false, false⟩,⟨26, [115,116,97,109,112,36,49,54,39,49], (some (16)), false, false, false⟩,⟨27, [115,116,97,109,112,36,49,54,39,48], (some (16)), false, false, false⟩,⟨28, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,49], (some (1)), false, false, false⟩,⟨29, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,50], (some (1)), false, false, false⟩,⟨30, [108,115,119,36,50,49], (some (1)), false, false, false⟩,⟨31, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,100,101,102,97,117,108,116], (some (1)), false, false, false⟩]

def C52_3p0 : List Nat := [24,10,115,116,97,109,112,36,49,53,39,48,1,16,0,0,0,0,0,0,25,10,115,116,97,109,112,36,49,54,39,50,1,16,0,0,0,0,0,0,26,10,115,116,97,109,112,36,49,54,39,49,1,16,0,0,0,0,0,0,27,10,115,116,97,109,112,36,49,54,39,48,1,16,0,0,0,0,0,0,28,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,49,1,1,0,0,0,0,0,0,29,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,50]
theorem C52_3p0bound : C52_3p0.all wordBound = true := (by decide : [24,10,115,116,97,109,112,36,49,53,39,48,1,16,0,0,0,0,0,0,25,10,115,116,97,109,112,36,49,54,39,50,1,16,0,0,0,0,0,0,26,10,115,116,97,109,112,36,49,54,39,49,1,16,0,0,0,0,0,0,27,10,115,116,97,109,112,36,49,54,39,48,1,16,0,0,0,0,0,0,28,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,49,1,1,0,0,0,0,0,0,29,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,50].all wordBound = true)

def C52_3p1 : List Nat := [1,1,0,0,0,0,0,0,30,6,108,115,119,36,50,49,1,1,0,0,0,0,0,0,31,24,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,100,101,102,97,117,108,116,1,1,0,0,0,0,0,0]
theorem C52_3p1bound : C52_3p1.all wordBound = true := (by decide : [1,1,0,0,0,0,0,0,30,6,108,115,119,36,50,49,1,1,0,0,0,0,0,0,31,24,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,100,101,102,97,117,108,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C52_3words : List Nat := C52_3p0 ++ C52_3p1

theorem C52_3wire : C52_3.flatMap columnWords = C52_3words := by
  rfl

theorem C52_3wordBound : C52_3words.all wordBound = true := by
  simp only [C52_3words,List.all_append,C52_3p0bound,C52_3p1bound]
  try rfl

theorem C52_3bounded : ∀ n ∈ C52_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C52_3wordBound

theorem C52_3length : C52_3.length = 8 := by rfl

def C52_4 : List Column := [⟨32, [99,36,52,56], (some (14)), false, false, false⟩,⟨33, [99,36,52,57], (some (14)), false, false, false⟩,⟨34, [99,36,53,48], (some (14)), false, false, false⟩,⟨35, [99,36,53,49], (some (14)), false, false, false⟩,⟨36, [99,36,53,50], (some (1)), false, false, false⟩,⟨37, [99,36,53,51], (some (1)), false, false, false⟩,⟨38, [99,36,53,52], (some (1)), false, false, false⟩,⟨39, [99,36,53,56], (some (1)), false, false, false⟩]

def C52_4p0 : List Nat := [32,4,99,36,52,56,1,14,0,0,0,0,0,0,33,4,99,36,52,57,1,14,0,0,0,0,0,0,34,4,99,36,53,48,1,14,0,0,0,0,0,0,35,4,99,36,53,49,1,14,0,0,0,0,0,0,36,4,99,36,53,50,1,1,0,0,0,0,0,0,37,4,99,36,53,51,1,1,0,0,0,0,0,0,38,4,99,36,53,52,1,1,0,0,0,0,0,0,39,4,99,36,53,56,1,1,0,0,0,0,0,0]
theorem C52_4p0bound : C52_4p0.all wordBound = true := (by decide : [32,4,99,36,52,56,1,14,0,0,0,0,0,0,33,4,99,36,52,57,1,14,0,0,0,0,0,0,34,4,99,36,53,48,1,14,0,0,0,0,0,0,35,4,99,36,53,49,1,14,0,0,0,0,0,0,36,4,99,36,53,50,1,1,0,0,0,0,0,0,37,4,99,36,53,51,1,1,0,0,0,0,0,0,38,4,99,36,53,52,1,1,0,0,0,0,0,0,39,4,99,36,53,56,1,1,0,0,0,0,0,0].all wordBound = true)

def C52_4words : List Nat := C52_4p0

theorem C52_4wire : C52_4.flatMap columnWords = C52_4words := by
  rfl

theorem C52_4wordBound : C52_4words.all wordBound = true := by
  simp only [C52_4words,List.all_append,C52_4p0bound]
  try rfl

theorem C52_4bounded : ∀ n ∈ C52_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C52_4wordBound

theorem C52_4length : C52_4.length = 8 := by rfl

def C52_5 : List Column := [⟨40, [36,114,101,116], (some (1)), false, false, false⟩,⟨41, [36,108,111,111,107,117,112,95,115,101,108,95,52,49], (some (1)), false, false, false⟩,⟨42, [36,108,111,111,107,117,112,95,115,101,108,95,52,50], (some (1)), false, false, false⟩,⟨43, [36,108,111,111,107,117,112,95,115,101,108,95,52,51], (some (1)), false, false, false⟩,⟨44, [40,105,110,118,32,119,114,105,116,101,95,49,54,58,98,111,102,102,115,101,116,41], none, false, false, true⟩,⟨45, [40,105,110,118,32,40,45,32,119,114,105,116,101,95,49,54,58,98,111,102,102,115,101,116,32,50,41,41], none, false, false, true⟩]

def C52_5p0 : List Nat := [40,4,36,114,101,116,1,1,0,0,0,0,0,0,41,14,36,108,111,111,107,117,112,95,115,101,108,95,52,49,1,1,0,0,0,0,0,0,42,14,36,108,111,111,107,117,112,95,115,101,108,95,52,50,1,1,0,0,0,0,0,0,43,14,36,108,111,111,107,117,112,95,115,101,108,95,52,51,1,1,0,0,0,0,0,0,44,22,40,105,110,118,32,119,114,105,116,101,95,49,54,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0,45,28,40,105,110,118,32,40,45,32]
theorem C52_5p0bound : C52_5p0.all wordBound = true := (by decide : [40,4,36,114,101,116,1,1,0,0,0,0,0,0,41,14,36,108,111,111,107,117,112,95,115,101,108,95,52,49,1,1,0,0,0,0,0,0,42,14,36,108,111,111,107,117,112,95,115,101,108,95,52,50,1,1,0,0,0,0,0,0,43,14,36,108,111,111,107,117,112,95,115,101,108,95,52,51,1,1,0,0,0,0,0,0,44,22,40,105,110,118,32,119,114,105,116,101,95,49,54,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0,45,28,40,105,110,118,32,40,45,32].all wordBound = true)

def C52_5p1 : List Nat := [119,114,105,116,101,95,49,54,58,98,111,102,102,115,101,116,32,50,41,41,0,0,0,0,0,0,1,0]
theorem C52_5p1bound : C52_5p1.all wordBound = true := (by decide : [119,114,105,116,101,95,49,54,58,98,111,102,102,115,101,116,32,50,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C52_5words : List Nat := C52_5p0 ++ C52_5p1

theorem C52_5wire : C52_5.flatMap columnWords = C52_5words := by
  rfl

theorem C52_5wordBound : C52_5words.all wordBound = true := by
  simp only [C52_5words,List.all_append,C52_5p0bound,C52_5p1bound]
  try rfl

theorem C52_5bounded : ∀ n ∈ C52_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C52_5wordBound

theorem C52_5length : C52_5.length = 6 := by rfl

def M52 : Module := ⟨52, [119,114,105,116,101,95,49,54], false, false, C52_0 ++ C52_1 ++ C52_2 ++ C52_3 ++ C52_4 ++ C52_5, ((List.range 0).map (fun n => [n]))⟩

def M52prefix : List Nat := [52,8,119,114,105,116,101,95,49,54,0,0,0,0,46]
theorem M52prefixwordBound : M52prefix.all wordBound = true := by decide

def M52words : List Nat := M52prefix ++ C52_0words ++ C52_1words ++ C52_2words ++ C52_3words ++ C52_4words ++ C52_5words ++ [0]

theorem M52wire : module.encode M52 = M52words := by
  rw [module_fast]
  simp only [M52,moduleWords,List.length_append,List.flatMap_append,C52_0length,C52_1length,C52_2length,C52_3length,C52_4length,C52_5length,C52_0wire,C52_1wire,C52_2wire,C52_3wire,C52_4wire,C52_5wire]
  rfl

theorem M52wordBound : M52words.all wordBound = true := by
  simp only [M52words,List.all_append,M52prefixwordBound,C52_0wordBound,C52_1wordBound,C52_2wordBound,C52_3wordBound,C52_4wordBound,C52_5wordBound]
  decide

theorem M52bounded : ∀ n ∈ M52words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M52wordBound

end DivRemFV.Replay
