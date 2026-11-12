import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C50_0 : List Column := [⟨0, [114,97,109,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨1, [114,97,109,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨2, [114,97,109,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨3, [97,100,100,114,101,115,115,39,51], (some (16)), true, false, false⟩,⟨4, [97,100,100,114,101,115,115,39,50], (some (16)), true, false, false⟩,⟨5, [97,100,100,114,101,115,115,39,49], (some (16)), true, false, false⟩,⟨6, [97,100,100,114,101,115,115,39,48], (some (16)), true, false, false⟩,⟨7, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,50], (some (16)), false, true, false⟩]

def C50_0p0 : List Nat := [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115]
theorem C50_0p0bound : C50_0p0.all wordBound = true := (by decide : [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115].all wordBound = true)

def C50_0p1 : List Nat := [115,39,48,1,16,1,0,0,0,0,0,7,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0]
theorem C50_0p1bound : C50_0p1.all wordBound = true := (by decide : [115,39,48,1,16,1,0,0,0,0,0,7,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0].all wordBound = true)

def C50_0words : List Nat := C50_0p0 ++ C50_0p1

theorem C50_0wire : C50_0.flatMap columnWords = C50_0words := by
  rfl

theorem C50_0wordBound : C50_0words.all wordBound = true := by
  simp only [C50_0words,List.all_append,C50_0p0bound,C50_0p1bound]
  try rfl

theorem C50_0bounded : ∀ n ∈ C50_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C50_0wordBound

theorem C50_0length : C50_0.length = 8 := by rfl

def C50_1 : List Column := [⟨8, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨9, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨10, [118,97,108,117,101,39,51], (some (16)), false, true, false⟩,⟨11, [118,97,108,117,101,39,50], (some (16)), false, true, false⟩,⟨12, [118,97,108,117,101,39,49], (some (16)), false, true, false⟩,⟨13, [118,97,108,117,101,39,48], (some (16)), false, true, false⟩,⟨14, [98,111,102,102,115,101,116], (some (2)), false, false, false⟩,⟨15, [119,111,102,102,115,101,116,39,51], (some (14)), false, false, false⟩]

def C50_1p0 : List Nat := [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,10,7,118,97,108,117,101,39,51,1,16,0,0,1,0,0,0,11,7,118,97,108,117,101,39,50,1,16,0,0,1,0,0,0,12,7,118,97,108,117,101,39,49,1,16,0,0,1,0,0,0,13,7,118,97,108,117,101,39,48,1,16,0,0,1,0,0,0,14,7,98,111,102,102,115,101,116,1]
theorem C50_1p0bound : C50_1p0.all wordBound = true := (by decide : [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,10,7,118,97,108,117,101,39,51,1,16,0,0,1,0,0,0,11,7,118,97,108,117,101,39,50,1,16,0,0,1,0,0,0,12,7,118,97,108,117,101,39,49,1,16,0,0,1,0,0,0,13,7,118,97,108,117,101,39,48,1,16,0,0,1,0,0,0,14,7,98,111,102,102,115,101,116,1].all wordBound = true)

def C50_1p1 : List Nat := [2,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0]
theorem C50_1p1bound : C50_1p1.all wordBound = true := (by decide : [2,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0].all wordBound = true)

def C50_1words : List Nat := C50_1p0 ++ C50_1p1

theorem C50_1wire : C50_1.flatMap columnWords = C50_1words := by
  rfl

theorem C50_1wordBound : C50_1words.all wordBound = true := by
  simp only [C50_1words,List.all_append,C50_1p0bound,C50_1p1bound]
  try rfl

theorem C50_1bounded : ∀ n ∈ C50_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C50_1wordBound

theorem C50_1length : C50_1.length = 8 := by rfl

def C50_2 : List Column := [⟨16, [119,111,102,102,115,101,116,39,50], (some (16)), false, false, false⟩,⟨17, [119,111,102,102,115,101,116,39,49], (some (16)), false, false, false⟩,⟨18, [119,111,102,102,115,101,116,39,48], (some (16)), false, false, false⟩,⟨19, [108,111,39,49], (some (16)), false, false, false⟩,⟨20, [108,111,39,48], (some (16)), false, false, false⟩,⟨21, [104,105,39,49], (some (16)), false, false, false⟩,⟨22, [104,105,39,48], (some (16)), false, false, false⟩,⟨23, [36,55,39,49], (some (16)), false, false, false⟩]

def C50_2p0 : List Nat := [16,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0,0,0,17,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0,18,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0,19,4,108,111,39,49,1,16,0,0,0,0,0,0,20,4,108,111,39,48,1,16,0,0,0,0,0,0,21,4,104,105,39,49,1,16,0,0,0,0,0,0,22,4,104,105,39,48,1,16,0,0,0,0,0,0,23,4,36,55,39,49,1,16,0,0,0,0,0,0]
theorem C50_2p0bound : C50_2p0.all wordBound = true := (by decide : [16,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0,0,0,17,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0,18,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0,19,4,108,111,39,49,1,16,0,0,0,0,0,0,20,4,108,111,39,48,1,16,0,0,0,0,0,0,21,4,104,105,39,49,1,16,0,0,0,0,0,0,22,4,104,105,39,48,1,16,0,0,0,0,0,0,23,4,36,55,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C50_2words : List Nat := C50_2p0

theorem C50_2wire : C50_2.flatMap columnWords = C50_2words := by
  rfl

theorem C50_2wordBound : C50_2words.all wordBound = true := by
  simp only [C50_2words,List.all_append,C50_2p0bound]
  try rfl

theorem C50_2bounded : ∀ n ∈ C50_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C50_2wordBound

theorem C50_2length : C50_2.length = 8 := by rfl

def C50_3 : List Column := [⟨24, [36,55,39,48], (some (16)), false, false, false⟩,⟨25, [36,56,39,49], (some (16)), false, false, false⟩,⟨26, [36,56,39,48], (some (16)), false, false, false⟩,⟨27, [115,116,97,109,112,36,49,50,39,50], (some (16)), false, false, false⟩,⟨28, [115,116,97,109,112,36,49,50,39,49], (some (16)), false, false, false⟩,⟨29, [115,116,97,109,112,36,49,50,39,48], (some (16)), false, false, false⟩,⟨30, [115,116,97,109,112,36,49,52,39,50], (some (16)), false, false, false⟩,⟨31, [115,116,97,109,112,36,49,52,39,49], (some (16)), false, false, false⟩]

def C50_3p0 : List Nat := [24,4,36,55,39,48,1,16,0,0,0,0,0,0,25,4,36,56,39,49,1,16,0,0,0,0,0,0,26,4,36,56,39,48,1,16,0,0,0,0,0,0,27,10,115,116,97,109,112,36,49,50,39,50,1,16,0,0,0,0,0,0,28,10,115,116,97,109,112,36,49,50,39,49,1,16,0,0,0,0,0,0,29,10,115,116,97,109,112,36,49,50,39,48,1,16,0,0,0,0,0,0,30,10,115,116,97,109,112,36,49,52,39,50,1,16,0,0,0,0,0,0,31,10,115,116,97,109]
theorem C50_3p0bound : C50_3p0.all wordBound = true := (by decide : [24,4,36,55,39,48,1,16,0,0,0,0,0,0,25,4,36,56,39,49,1,16,0,0,0,0,0,0,26,4,36,56,39,48,1,16,0,0,0,0,0,0,27,10,115,116,97,109,112,36,49,50,39,50,1,16,0,0,0,0,0,0,28,10,115,116,97,109,112,36,49,50,39,49,1,16,0,0,0,0,0,0,29,10,115,116,97,109,112,36,49,50,39,48,1,16,0,0,0,0,0,0,30,10,115,116,97,109,112,36,49,52,39,50,1,16,0,0,0,0,0,0,31,10,115,116,97,109].all wordBound = true)

def C50_3p1 : List Nat := [112,36,49,52,39,49,1,16,0,0,0,0,0,0]
theorem C50_3p1bound : C50_3p1.all wordBound = true := (by decide : [112,36,49,52,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C50_3words : List Nat := C50_3p0 ++ C50_3p1

theorem C50_3wire : C50_3.flatMap columnWords = C50_3words := by
  rfl

theorem C50_3wordBound : C50_3words.all wordBound = true := by
  simp only [C50_3words,List.all_append,C50_3p0bound,C50_3p1bound]
  try rfl

theorem C50_3bounded : ∀ n ∈ C50_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C50_3wordBound

theorem C50_3length : C50_3.length = 8 := by rfl

def C50_4 : List Column := [⟨32, [115,116,97,109,112,36,49,52,39,48], (some (16)), false, false, false⟩,⟨33, [102,115,99,36,49,53], (some (1)), false, false, false⟩,⟨34, [99,36,52,53], (some (14)), false, false, false⟩,⟨35, [99,36,52,54], (some (14)), false, false, false⟩,⟨36, [99,36,52,55], (some (14)), false, false, false⟩,⟨37, [99,36,52,56], (some (14)), false, false, false⟩,⟨38, [99,36,52,57], (some (1)), false, false, false⟩,⟨39, [99,36,53,48], (some (1)), false, false, false⟩]

def C50_4p0 : List Nat := [32,10,115,116,97,109,112,36,49,52,39,48,1,16,0,0,0,0,0,0,33,6,102,115,99,36,49,53,1,1,0,0,0,0,0,0,34,4,99,36,52,53,1,14,0,0,0,0,0,0,35,4,99,36,52,54,1,14,0,0,0,0,0,0,36,4,99,36,52,55,1,14,0,0,0,0,0,0,37,4,99,36,52,56,1,14,0,0,0,0,0,0,38,4,99,36,52,57,1,1,0,0,0,0,0,0,39,4,99,36,53,48,1,1,0,0,0,0,0,0]
theorem C50_4p0bound : C50_4p0.all wordBound = true := (by decide : [32,10,115,116,97,109,112,36,49,52,39,48,1,16,0,0,0,0,0,0,33,6,102,115,99,36,49,53,1,1,0,0,0,0,0,0,34,4,99,36,52,53,1,14,0,0,0,0,0,0,35,4,99,36,52,54,1,14,0,0,0,0,0,0,36,4,99,36,52,55,1,14,0,0,0,0,0,0,37,4,99,36,52,56,1,14,0,0,0,0,0,0,38,4,99,36,52,57,1,1,0,0,0,0,0,0,39,4,99,36,53,48,1,1,0,0,0,0,0,0].all wordBound = true)

def C50_4words : List Nat := C50_4p0

theorem C50_4wire : C50_4.flatMap columnWords = C50_4words := by
  rfl

theorem C50_4wordBound : C50_4words.all wordBound = true := by
  simp only [C50_4words,List.all_append,C50_4p0bound]
  try rfl

theorem C50_4bounded : ∀ n ∈ C50_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C50_4wordBound

theorem C50_4length : C50_4.length = 8 := by rfl

def C50_5 : List Column := [⟨40, [99,36,53,49], (some (1)), false, false, false⟩,⟨41, [99,36,53,50], (some (1)), false, false, false⟩,⟨42, [99,36,53,51], (some (1)), false, false, false⟩,⟨43, [99,36,53,52], (some (1)), false, false, false⟩,⟨44, [99,36,53,53], (some (1)), false, false, false⟩,⟨45, [36,114,101,116], (some (1)), false, false, false⟩,⟨46, [36,108,111,111,107,117,112,95,115,101,108,95,52,54], (some (1)), false, false, false⟩,⟨47, [36,108,111,111,107,117,112,95,115,101,108,95,52,55], (some (1)), false, false, false⟩]

def C50_5p0 : List Nat := [40,4,99,36,53,49,1,1,0,0,0,0,0,0,41,4,99,36,53,50,1,1,0,0,0,0,0,0,42,4,99,36,53,51,1,1,0,0,0,0,0,0,43,4,99,36,53,52,1,1,0,0,0,0,0,0,44,4,99,36,53,53,1,1,0,0,0,0,0,0,45,4,36,114,101,116,1,1,0,0,0,0,0,0,46,14,36,108,111,111,107,117,112,95,115,101,108,95,52,54,1,1,0,0,0,0,0,0,47,14,36,108,111,111,107,117,112,95,115,101,108,95,52,55,1,1,0,0]
theorem C50_5p0bound : C50_5p0.all wordBound = true := (by decide : [40,4,99,36,53,49,1,1,0,0,0,0,0,0,41,4,99,36,53,50,1,1,0,0,0,0,0,0,42,4,99,36,53,51,1,1,0,0,0,0,0,0,43,4,99,36,53,52,1,1,0,0,0,0,0,0,44,4,99,36,53,53,1,1,0,0,0,0,0,0,45,4,36,114,101,116,1,1,0,0,0,0,0,0,46,14,36,108,111,111,107,117,112,95,115,101,108,95,52,54,1,1,0,0,0,0,0,0,47,14,36,108,111,111,107,117,112,95,115,101,108,95,52,55,1,1,0,0].all wordBound = true)

def C50_5p1 : List Nat := [0,0,0,0]
theorem C50_5p1bound : C50_5p1.all wordBound = true := (by decide : [0,0,0,0].all wordBound = true)

def C50_5words : List Nat := C50_5p0 ++ C50_5p1

theorem C50_5wire : C50_5.flatMap columnWords = C50_5words := by
  rfl

theorem C50_5wordBound : C50_5words.all wordBound = true := by
  simp only [C50_5words,List.all_append,C50_5p0bound,C50_5p1bound]
  try rfl

theorem C50_5bounded : ∀ n ∈ C50_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C50_5wordBound

theorem C50_5length : C50_5.length = 8 := by rfl

def C50_6 : List Column := [⟨48, [40,105,110,118,32,114,101,97,100,95,54,52,58,98,111,102,102,115,101,116,41], none, false, false, true⟩]

def C50_6p0 : List Nat := [48,21,40,105,110,118,32,114,101,97,100,95,54,52,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0]
theorem C50_6p0bound : C50_6p0.all wordBound = true := (by decide : [48,21,40,105,110,118,32,114,101,97,100,95,54,52,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C50_6words : List Nat := C50_6p0

theorem C50_6wire : C50_6.flatMap columnWords = C50_6words := by
  rfl

theorem C50_6wordBound : C50_6words.all wordBound = true := by
  simp only [C50_6words,List.all_append,C50_6p0bound]
  try rfl

theorem C50_6bounded : ∀ n ∈ C50_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C50_6wordBound

theorem C50_6length : C50_6.length = 1 := by rfl

def M50 : Module := ⟨50, [114,101,97,100,95,54,52], false, false, C50_0 ++ C50_1 ++ C50_2 ++ C50_3 ++ C50_4 ++ C50_5 ++ C50_6, ((List.range 0).map (fun n => [n]))⟩

def M50prefix : List Nat := [50,7,114,101,97,100,95,54,52,0,0,0,0,49]
theorem M50prefixwordBound : M50prefix.all wordBound = true := by decide

def M50words : List Nat := M50prefix ++ C50_0words ++ C50_1words ++ C50_2words ++ C50_3words ++ C50_4words ++ C50_5words ++ C50_6words ++ [0]

theorem M50wire : module.encode M50 = M50words := by
  rw [module_fast]
  simp only [M50,moduleWords,List.length_append,List.flatMap_append,C50_0length,C50_1length,C50_2length,C50_3length,C50_4length,C50_5length,C50_6length,C50_0wire,C50_1wire,C50_2wire,C50_3wire,C50_4wire,C50_5wire,C50_6wire]
  rfl

theorem M50wordBound : M50words.all wordBound = true := by
  simp only [M50words,List.all_append,M50prefixwordBound,C50_0wordBound,C50_1wordBound,C50_2wordBound,C50_3wordBound,C50_4wordBound,C50_5wordBound,C50_6wordBound]
  decide

theorem M50bounded : ∀ n ∈ M50words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M50wordBound

end DivRemFV.Replay
