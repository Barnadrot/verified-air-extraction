import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C54_0 : List Column := [⟨0, [114,97,109,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨1, [114,97,109,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨2, [114,97,109,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨3, [97,100,100,114,101,115,115,39,51], (some (16)), true, false, false⟩,⟨4, [97,100,100,114,101,115,115,39,50], (some (16)), true, false, false⟩,⟨5, [97,100,100,114,101,115,115,39,49], (some (16)), true, false, false⟩,⟨6, [97,100,100,114,101,115,115,39,48], (some (16)), true, false, false⟩,⟨7, [118,97,108,117,101,39,51], (some (16)), true, false, false⟩]

def C54_0p0 : List Nat := [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115]
theorem C54_0p0bound : C54_0p0.all wordBound = true := (by decide : [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115].all wordBound = true)

def C54_0p1 : List Nat := [115,39,48,1,16,1,0,0,0,0,0,7,7,118,97,108,117,101,39,51,1,16,1,0,0,0,0,0]
theorem C54_0p1bound : C54_0p1.all wordBound = true := (by decide : [115,39,48,1,16,1,0,0,0,0,0,7,7,118,97,108,117,101,39,51,1,16,1,0,0,0,0,0].all wordBound = true)

def C54_0words : List Nat := C54_0p0 ++ C54_0p1

theorem C54_0wire : C54_0.flatMap columnWords = C54_0words := by
  rfl

theorem C54_0wordBound : C54_0words.all wordBound = true := by
  simp only [C54_0words,List.all_append,C54_0p0bound,C54_0p1bound]
  try rfl

theorem C54_0bounded : ∀ n ∈ C54_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C54_0wordBound

theorem C54_0length : C54_0.length = 8 := by rfl

def C54_1 : List Column := [⟨8, [118,97,108,117,101,39,50], (some (16)), true, false, false⟩,⟨9, [118,97,108,117,101,39,49], (some (16)), true, false, false⟩,⟨10, [118,97,108,117,101,39,48], (some (16)), true, false, false⟩,⟨11, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,50], (some (16)), false, true, false⟩,⟨12, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨13, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨14, [98,111,102,102,115,101,116], (some (2)), false, false, false⟩,⟨15, [119,111,102,102,115,101,116,39,51], (some (14)), false, false, false⟩]

def C54_1p0 : List Nat := [8,7,118,97,108,117,101,39,50,1,16,1,0,0,0,0,0,9,7,118,97,108,117,101,39,49,1,16,1,0,0,0,0,0,10,7,118,97,108,117,101,39,48,1,16,1,0,0,0,0,0,11,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,12,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,13,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,14,7]
theorem C54_1p0bound : C54_1p0.all wordBound = true := (by decide : [8,7,118,97,108,117,101,39,50,1,16,1,0,0,0,0,0,9,7,118,97,108,117,101,39,49,1,16,1,0,0,0,0,0,10,7,118,97,108,117,101,39,48,1,16,1,0,0,0,0,0,11,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,12,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,13,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,14,7].all wordBound = true)

def C54_1p1 : List Nat := [98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0]
theorem C54_1p1bound : C54_1p1.all wordBound = true := (by decide : [98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0].all wordBound = true)

def C54_1words : List Nat := C54_1p0 ++ C54_1p1

theorem C54_1wire : C54_1.flatMap columnWords = C54_1words := by
  rfl

theorem C54_1wordBound : C54_1words.all wordBound = true := by
  simp only [C54_1words,List.all_append,C54_1p0bound,C54_1p1bound]
  try rfl

theorem C54_1bounded : ∀ n ∈ C54_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C54_1wordBound

theorem C54_1length : C54_1.length = 8 := by rfl

def C54_2 : List Column := [⟨16, [119,111,102,102,115,101,116,39,50], (some (16)), false, false, false⟩,⟨17, [119,111,102,102,115,101,116,39,49], (some (16)), false, false, false⟩,⟨18, [119,111,102,102,115,101,116,39,48], (some (16)), false, false, false⟩,⟨19, [108,111,39,49], (some (16)), false, false, false⟩,⟨20, [108,111,39,48], (some (16)), false, false, false⟩,⟨21, [104,105,39,49], (some (16)), false, false, false⟩,⟨22, [104,105,39,48], (some (16)), false, false, false⟩,⟨23, [36,54,39,51], (some (16)), false, false, false⟩]

def C54_2p0 : List Nat := [16,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0,0,0,17,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0,18,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0,19,4,108,111,39,49,1,16,0,0,0,0,0,0,20,4,108,111,39,48,1,16,0,0,0,0,0,0,21,4,104,105,39,49,1,16,0,0,0,0,0,0,22,4,104,105,39,48,1,16,0,0,0,0,0,0,23,4,36,54,39,51,1,16,0,0,0,0,0,0]
theorem C54_2p0bound : C54_2p0.all wordBound = true := (by decide : [16,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0,0,0,17,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0,18,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0,19,4,108,111,39,49,1,16,0,0,0,0,0,0,20,4,108,111,39,48,1,16,0,0,0,0,0,0,21,4,104,105,39,49,1,16,0,0,0,0,0,0,22,4,104,105,39,48,1,16,0,0,0,0,0,0,23,4,36,54,39,51,1,16,0,0,0,0,0,0].all wordBound = true)

def C54_2words : List Nat := C54_2p0

theorem C54_2wire : C54_2.flatMap columnWords = C54_2words := by
  rfl

theorem C54_2wordBound : C54_2words.all wordBound = true := by
  simp only [C54_2words,List.all_append,C54_2p0bound]
  try rfl

theorem C54_2bounded : ∀ n ∈ C54_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C54_2wordBound

theorem C54_2length : C54_2.length = 8 := by rfl

def C54_3 : List Column := [⟨24, [36,54,39,50], (some (16)), false, false, false⟩,⟨25, [36,54,39,49], (some (16)), false, false, false⟩,⟨26, [36,54,39,48], (some (16)), false, false, false⟩,⟨27, [115,116,97,109,112,36,49,48,39,50], (some (16)), false, false, false⟩,⟨28, [115,116,97,109,112,36,49,48,39,49], (some (16)), false, false, false⟩,⟨29, [115,116,97,109,112,36,49,48,39,48], (some (16)), false, false, false⟩,⟨30, [115,116,97,109,112,36,49,50,39,50], (some (16)), false, false, false⟩,⟨31, [115,116,97,109,112,36,49,50,39,49], (some (16)), false, false, false⟩]

def C54_3p0 : List Nat := [24,4,36,54,39,50,1,16,0,0,0,0,0,0,25,4,36,54,39,49,1,16,0,0,0,0,0,0,26,4,36,54,39,48,1,16,0,0,0,0,0,0,27,10,115,116,97,109,112,36,49,48,39,50,1,16,0,0,0,0,0,0,28,10,115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0,29,10,115,116,97,109,112,36,49,48,39,48,1,16,0,0,0,0,0,0,30,10,115,116,97,109,112,36,49,50,39,50,1,16,0,0,0,0,0,0,31,10,115,116,97,109]
theorem C54_3p0bound : C54_3p0.all wordBound = true := (by decide : [24,4,36,54,39,50,1,16,0,0,0,0,0,0,25,4,36,54,39,49,1,16,0,0,0,0,0,0,26,4,36,54,39,48,1,16,0,0,0,0,0,0,27,10,115,116,97,109,112,36,49,48,39,50,1,16,0,0,0,0,0,0,28,10,115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0,29,10,115,116,97,109,112,36,49,48,39,48,1,16,0,0,0,0,0,0,30,10,115,116,97,109,112,36,49,50,39,50,1,16,0,0,0,0,0,0,31,10,115,116,97,109].all wordBound = true)

def C54_3p1 : List Nat := [112,36,49,50,39,49,1,16,0,0,0,0,0,0]
theorem C54_3p1bound : C54_3p1.all wordBound = true := (by decide : [112,36,49,50,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C54_3words : List Nat := C54_3p0 ++ C54_3p1

theorem C54_3wire : C54_3.flatMap columnWords = C54_3words := by
  rfl

theorem C54_3wordBound : C54_3words.all wordBound = true := by
  simp only [C54_3words,List.all_append,C54_3p0bound,C54_3p1bound]
  try rfl

theorem C54_3bounded : ∀ n ∈ C54_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C54_3wordBound

theorem C54_3length : C54_3.length = 8 := by rfl

def C54_4 : List Column := [⟨32, [115,116,97,109,112,36,49,50,39,48], (some (16)), false, false, false⟩,⟨33, [102,115,99,36,49,51], (some (1)), false, false, false⟩,⟨34, [99,36,52,49], (some (14)), false, false, false⟩,⟨35, [99,36,52,50], (some (14)), false, false, false⟩,⟨36, [99,36,52,51], (some (14)), false, false, false⟩,⟨37, [99,36,52,52], (some (14)), false, false, false⟩,⟨38, [99,36,52,53], (some (1)), false, false, false⟩,⟨39, [99,36,52,54], (some (1)), false, false, false⟩]

def C54_4p0 : List Nat := [32,10,115,116,97,109,112,36,49,50,39,48,1,16,0,0,0,0,0,0,33,6,102,115,99,36,49,51,1,1,0,0,0,0,0,0,34,4,99,36,52,49,1,14,0,0,0,0,0,0,35,4,99,36,52,50,1,14,0,0,0,0,0,0,36,4,99,36,52,51,1,14,0,0,0,0,0,0,37,4,99,36,52,52,1,14,0,0,0,0,0,0,38,4,99,36,52,53,1,1,0,0,0,0,0,0,39,4,99,36,52,54,1,1,0,0,0,0,0,0]
theorem C54_4p0bound : C54_4p0.all wordBound = true := (by decide : [32,10,115,116,97,109,112,36,49,50,39,48,1,16,0,0,0,0,0,0,33,6,102,115,99,36,49,51,1,1,0,0,0,0,0,0,34,4,99,36,52,49,1,14,0,0,0,0,0,0,35,4,99,36,52,50,1,14,0,0,0,0,0,0,36,4,99,36,52,51,1,14,0,0,0,0,0,0,37,4,99,36,52,52,1,14,0,0,0,0,0,0,38,4,99,36,52,53,1,1,0,0,0,0,0,0,39,4,99,36,52,54,1,1,0,0,0,0,0,0].all wordBound = true)

def C54_4words : List Nat := C54_4p0

theorem C54_4wire : C54_4.flatMap columnWords = C54_4words := by
  rfl

theorem C54_4wordBound : C54_4words.all wordBound = true := by
  simp only [C54_4words,List.all_append,C54_4p0bound]
  try rfl

theorem C54_4bounded : ∀ n ∈ C54_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C54_4wordBound

theorem C54_4length : C54_4.length = 8 := by rfl

def C54_5 : List Column := [⟨40, [99,36,52,55], (some (1)), false, false, false⟩,⟨41, [99,36,52,56], (some (1)), false, false, false⟩,⟨42, [99,36,52,57], (some (1)), false, false, false⟩,⟨43, [99,36,53,48], (some (1)), false, false, false⟩,⟨44, [99,36,53,49], (some (1)), false, false, false⟩,⟨45, [36,114,101,116], (some (1)), false, false, false⟩,⟨46, [36,108,111,111,107,117,112,95,115,101,108,95,52,54], (some (1)), false, false, false⟩,⟨47, [36,108,111,111,107,117,112,95,115,101,108,95,52,55], (some (1)), false, false, false⟩]

def C54_5p0 : List Nat := [40,4,99,36,52,55,1,1,0,0,0,0,0,0,41,4,99,36,52,56,1,1,0,0,0,0,0,0,42,4,99,36,52,57,1,1,0,0,0,0,0,0,43,4,99,36,53,48,1,1,0,0,0,0,0,0,44,4,99,36,53,49,1,1,0,0,0,0,0,0,45,4,36,114,101,116,1,1,0,0,0,0,0,0,46,14,36,108,111,111,107,117,112,95,115,101,108,95,52,54,1,1,0,0,0,0,0,0,47,14,36,108,111,111,107,117,112,95,115,101,108,95,52,55,1,1,0,0]
theorem C54_5p0bound : C54_5p0.all wordBound = true := (by decide : [40,4,99,36,52,55,1,1,0,0,0,0,0,0,41,4,99,36,52,56,1,1,0,0,0,0,0,0,42,4,99,36,52,57,1,1,0,0,0,0,0,0,43,4,99,36,53,48,1,1,0,0,0,0,0,0,44,4,99,36,53,49,1,1,0,0,0,0,0,0,45,4,36,114,101,116,1,1,0,0,0,0,0,0,46,14,36,108,111,111,107,117,112,95,115,101,108,95,52,54,1,1,0,0,0,0,0,0,47,14,36,108,111,111,107,117,112,95,115,101,108,95,52,55,1,1,0,0].all wordBound = true)

def C54_5p1 : List Nat := [0,0,0,0]
theorem C54_5p1bound : C54_5p1.all wordBound = true := (by decide : [0,0,0,0].all wordBound = true)

def C54_5words : List Nat := C54_5p0 ++ C54_5p1

theorem C54_5wire : C54_5.flatMap columnWords = C54_5words := by
  rfl

theorem C54_5wordBound : C54_5words.all wordBound = true := by
  simp only [C54_5words,List.all_append,C54_5p0bound,C54_5p1bound]
  try rfl

theorem C54_5bounded : ∀ n ∈ C54_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C54_5wordBound

theorem C54_5length : C54_5.length = 8 := by rfl

def C54_6 : List Column := [⟨48, [40,105,110,118,32,119,114,105,116,101,95,54,52,58,98,111,102,102,115,101,116,41], none, false, false, true⟩]

def C54_6p0 : List Nat := [48,22,40,105,110,118,32,119,114,105,116,101,95,54,52,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0]
theorem C54_6p0bound : C54_6p0.all wordBound = true := (by decide : [48,22,40,105,110,118,32,119,114,105,116,101,95,54,52,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C54_6words : List Nat := C54_6p0

theorem C54_6wire : C54_6.flatMap columnWords = C54_6words := by
  rfl

theorem C54_6wordBound : C54_6words.all wordBound = true := by
  simp only [C54_6words,List.all_append,C54_6p0bound]
  try rfl

theorem C54_6bounded : ∀ n ∈ C54_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C54_6wordBound

theorem C54_6length : C54_6.length = 1 := by rfl

def M54 : Module := ⟨54, [119,114,105,116,101,95,54,52], false, false, C54_0 ++ C54_1 ++ C54_2 ++ C54_3 ++ C54_4 ++ C54_5 ++ C54_6, ((List.range 0).map (fun n => [n]))⟩

def M54prefix : List Nat := [54,8,119,114,105,116,101,95,54,52,0,0,0,0,49]
theorem M54prefixwordBound : M54prefix.all wordBound = true := by decide

def M54words : List Nat := M54prefix ++ C54_0words ++ C54_1words ++ C54_2words ++ C54_3words ++ C54_4words ++ C54_5words ++ C54_6words ++ [0]

theorem M54wire : module.encode M54 = M54words := by
  rw [module_fast]
  simp only [M54,moduleWords,List.length_append,List.flatMap_append,C54_0length,C54_1length,C54_2length,C54_3length,C54_4length,C54_5length,C54_6length,C54_0wire,C54_1wire,C54_2wire,C54_3wire,C54_4wire,C54_5wire,C54_6wire]
  rfl

theorem M54wordBound : M54words.all wordBound = true := by
  simp only [M54words,List.all_append,M54prefixwordBound,C54_0wordBound,C54_1wordBound,C54_2wordBound,C54_3wordBound,C54_4wordBound,C54_5wordBound,C54_6wordBound]
  decide

theorem M54bounded : ∀ n ∈ M54words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M54wordBound

end DivRemFV.Replay
