import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C63_0 : List Column := [⟨0, [97,39,49], (some (16)), true, false, false⟩,⟨1, [97,39,48], (some (16)), true, false, false⟩,⟨2, [98,39,49], (some (16)), true, false, false⟩,⟨3, [98,39,48], (some (16)), true, false, false⟩,⟨4, [113,39,49], (some (16)), false, true, false⟩,⟨5, [113,39,48], (some (16)), false, true, false⟩,⟨6, [114,39,49], (some (16)), false, true, false⟩,⟨7, [114,39,48], (some (16)), false, true, false⟩]

def C63_0p0 : List Nat := [0,3,97,39,49,1,16,1,0,0,0,0,0,1,3,97,39,48,1,16,1,0,0,0,0,0,2,3,98,39,49,1,16,1,0,0,0,0,0,3,3,98,39,48,1,16,1,0,0,0,0,0,4,3,113,39,49,1,16,0,0,1,0,0,0,5,3,113,39,48,1,16,0,0,1,0,0,0,6,3,114,39,49,1,16,0,0,1,0,0,0,7,3,114,39,48,1,16,0,0,1,0,0,0]
theorem C63_0p0bound : C63_0p0.all wordBound = true := (by decide : [0,3,97,39,49,1,16,1,0,0,0,0,0,1,3,97,39,48,1,16,1,0,0,0,0,0,2,3,98,39,49,1,16,1,0,0,0,0,0,3,3,98,39,48,1,16,1,0,0,0,0,0,4,3,113,39,49,1,16,0,0,1,0,0,0,5,3,113,39,48,1,16,0,0,1,0,0,0,6,3,114,39,49,1,16,0,0,1,0,0,0,7,3,114,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C63_0words : List Nat := C63_0p0

theorem C63_0wire : C63_0.flatMap columnWords = C63_0words := by
  rfl

theorem C63_0wordBound : C63_0words.all wordBound = true := by
  simp only [C63_0words,List.all_append,C63_0p0bound]
  try rfl

theorem C63_0bounded : ∀ n ∈ C63_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C63_0wordBound

theorem C63_0length : C63_0.length = 8 := by rfl

def C63_1 : List Column := [⟨8, [119,36,52,39,49], (some (16)), false, false, false⟩,⟨9, [119,36,52,39,48], (some (16)), false, false, false⟩,⟨10, [113,121,36,53,39,49], (some (16)), false, false, false⟩,⟨11, [113,121,36,53,39,48], (some (16)), false, false, false⟩,⟨12, [113,121,95,112,108,117,115,95,114,36,54,39,49], (some (16)), false, false, false⟩,⟨13, [113,121,95,112,108,117,115,95,114,36,54,39,48], (some (16)), false, false, false⟩,⟨14, [114,119,49,36,55,39,49], (some (16)), false, false, false⟩,⟨15, [114,119,49,36,55,39,48], (some (16)), false, false, false⟩]

def C63_1p0 : List Nat := [8,5,119,36,52,39,49,1,16,0,0,0,0,0,0,9,5,119,36,52,39,48,1,16,0,0,0,0,0,0,10,6,113,121,36,53,39,49,1,16,0,0,0,0,0,0,11,6,113,121,36,53,39,48,1,16,0,0,0,0,0,0,12,13,113,121,95,112,108,117,115,95,114,36,54,39,49,1,16,0,0,0,0,0,0,13,13,113,121,95,112,108,117,115,95,114,36,54,39,48,1,16,0,0,0,0,0,0,14,7,114,119,49,36,55,39,49,1,16,0,0,0,0,0,0,15,7,114]
theorem C63_1p0bound : C63_1p0.all wordBound = true := (by decide : [8,5,119,36,52,39,49,1,16,0,0,0,0,0,0,9,5,119,36,52,39,48,1,16,0,0,0,0,0,0,10,6,113,121,36,53,39,49,1,16,0,0,0,0,0,0,11,6,113,121,36,53,39,48,1,16,0,0,0,0,0,0,12,13,113,121,95,112,108,117,115,95,114,36,54,39,49,1,16,0,0,0,0,0,0,13,13,113,121,95,112,108,117,115,95,114,36,54,39,48,1,16,0,0,0,0,0,0,14,7,114,119,49,36,55,39,49,1,16,0,0,0,0,0,0,15,7,114].all wordBound = true)

def C63_1p1 : List Nat := [119,49,36,55,39,48,1,16,0,0,0,0,0,0]
theorem C63_1p1bound : C63_1p1.all wordBound = true := (by decide : [119,49,36,55,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C63_1words : List Nat := C63_1p0 ++ C63_1p1

theorem C63_1wire : C63_1.flatMap columnWords = C63_1words := by
  rfl

theorem C63_1wordBound : C63_1words.all wordBound = true := by
  simp only [C63_1words,List.all_append,C63_1p0bound,C63_1p1bound]
  try rfl

theorem C63_1bounded : ∀ n ∈ C63_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C63_1wordBound

theorem C63_1length : C63_1.length = 8 := by rfl

def C63_2 : List Column := [⟨16, [36,99,115,116,95,48], (some (0)), false, false, false⟩,⟨17, [102,115,99,36,57], (some (1)), false, false, false⟩,⟨18, [115,36,49,56], (some (15)), false, false, false⟩,⟨19, [115,36,49,57], (some (1)), false, false, false⟩,⟨20, [115,36,50,48], (some (14)), false, false, false⟩,⟨21, [115,36,50,49], (some (2)), false, false, false⟩,⟨22, [115,36,50,50], (some (15)), false, false, false⟩,⟨23, [115,36,50,51], (some (15)), false, false, false⟩]

def C63_2p0 : List Nat := [16,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,17,5,102,115,99,36,57,1,1,0,0,0,0,0,0,18,4,115,36,49,56,1,15,0,0,0,0,0,0,19,4,115,36,49,57,1,1,0,0,0,0,0,0,20,4,115,36,50,48,1,14,0,0,0,0,0,0,21,4,115,36,50,49,1,2,0,0,0,0,0,0,22,4,115,36,50,50,1,15,0,0,0,0,0,0,23,4,115,36,50,51,1,15,0,0,0,0,0,0]
theorem C63_2p0bound : C63_2p0.all wordBound = true := (by decide : [16,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,17,5,102,115,99,36,57,1,1,0,0,0,0,0,0,18,4,115,36,49,56,1,15,0,0,0,0,0,0,19,4,115,36,49,57,1,1,0,0,0,0,0,0,20,4,115,36,50,48,1,14,0,0,0,0,0,0,21,4,115,36,50,49,1,2,0,0,0,0,0,0,22,4,115,36,50,50,1,15,0,0,0,0,0,0,23,4,115,36,50,51,1,15,0,0,0,0,0,0].all wordBound = true)

def C63_2words : List Nat := C63_2p0

theorem C63_2wire : C63_2.flatMap columnWords = C63_2words := by
  rfl

theorem C63_2wordBound : C63_2words.all wordBound = true := by
  simp only [C63_2words,List.all_append,C63_2p0bound]
  try rfl

theorem C63_2bounded : ∀ n ∈ C63_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C63_2wordBound

theorem C63_2length : C63_2.length = 8 := by rfl

def C63_3 : List Column := [⟨24, [115,36,50,52], (some (1)), false, false, false⟩,⟨25, [115,36,50,53], (some (14)), false, false, false⟩,⟨26, [115,36,50,54], (some (2)), false, false, false⟩,⟨27, [115,36,50,55], (some (15)), false, false, false⟩,⟨28, [112,112,36,50,56], (some (15)), false, false, false⟩,⟨29, [112,112,36,50,57], (some (15)), false, false, false⟩,⟨30, [112,112,36,51,48], (some (15)), false, false, false⟩,⟨31, [112,112,36,51,49], (some (15)), false, false, false⟩]

def C63_3p0 : List Nat := [24,4,115,36,50,52,1,1,0,0,0,0,0,0,25,4,115,36,50,53,1,14,0,0,0,0,0,0,26,4,115,36,50,54,1,2,0,0,0,0,0,0,27,4,115,36,50,55,1,15,0,0,0,0,0,0,28,5,112,112,36,50,56,1,15,0,0,0,0,0,0,29,5,112,112,36,50,57,1,15,0,0,0,0,0,0,30,5,112,112,36,51,48,1,15,0,0,0,0,0,0,31,5,112,112,36,51,49,1,15,0,0,0,0,0,0]
theorem C63_3p0bound : C63_3p0.all wordBound = true := (by decide : [24,4,115,36,50,52,1,1,0,0,0,0,0,0,25,4,115,36,50,53,1,14,0,0,0,0,0,0,26,4,115,36,50,54,1,2,0,0,0,0,0,0,27,4,115,36,50,55,1,15,0,0,0,0,0,0,28,5,112,112,36,50,56,1,15,0,0,0,0,0,0,29,5,112,112,36,50,57,1,15,0,0,0,0,0,0,30,5,112,112,36,51,48,1,15,0,0,0,0,0,0,31,5,112,112,36,51,49,1,15,0,0,0,0,0,0].all wordBound = true)

def C63_3words : List Nat := C63_3p0

theorem C63_3wire : C63_3.flatMap columnWords = C63_3words := by
  rfl

theorem C63_3wordBound : C63_3words.all wordBound = true := by
  simp only [C63_3words,List.all_append,C63_3p0bound]
  try rfl

theorem C63_3bounded : ∀ n ∈ C63_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C63_3wordBound

theorem C63_3length : C63_3.length = 8 := by rfl

def C63_4 : List Column := [⟨32, [112,112,36,51,50], (some (15)), false, false, false⟩,⟨33, [112,112,36,51,51], (some (2)), false, false, false⟩,⟨34, [112,112,36,51,52], (some (15)), false, false, false⟩,⟨35, [112,112,36,51,53], (some (15)), false, false, false⟩,⟨36, [112,112,36,51,54], (some (15)), false, false, false⟩,⟨37, [112,112,36,51,55], (some (15)), false, false, false⟩,⟨38, [112,112,36,51,56], (some (15)), false, false, false⟩,⟨39, [112,112,36,51,57], (some (2)), false, false, false⟩]

def C63_4p0 : List Nat := [32,5,112,112,36,51,50,1,15,0,0,0,0,0,0,33,5,112,112,36,51,51,1,2,0,0,0,0,0,0,34,5,112,112,36,51,52,1,15,0,0,0,0,0,0,35,5,112,112,36,51,53,1,15,0,0,0,0,0,0,36,5,112,112,36,51,54,1,15,0,0,0,0,0,0,37,5,112,112,36,51,55,1,15,0,0,0,0,0,0,38,5,112,112,36,51,56,1,15,0,0,0,0,0,0,39,5,112,112,36,51,57,1,2,0,0,0,0,0,0]
theorem C63_4p0bound : C63_4p0.all wordBound = true := (by decide : [32,5,112,112,36,51,50,1,15,0,0,0,0,0,0,33,5,112,112,36,51,51,1,2,0,0,0,0,0,0,34,5,112,112,36,51,52,1,15,0,0,0,0,0,0,35,5,112,112,36,51,53,1,15,0,0,0,0,0,0,36,5,112,112,36,51,54,1,15,0,0,0,0,0,0,37,5,112,112,36,51,55,1,15,0,0,0,0,0,0,38,5,112,112,36,51,56,1,15,0,0,0,0,0,0,39,5,112,112,36,51,57,1,2,0,0,0,0,0,0].all wordBound = true)

def C63_4words : List Nat := C63_4p0

theorem C63_4wire : C63_4.flatMap columnWords = C63_4words := by
  rfl

theorem C63_4wordBound : C63_4words.all wordBound = true := by
  simp only [C63_4words,List.all_append,C63_4p0bound]
  try rfl

theorem C63_4bounded : ∀ n ∈ C63_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C63_4wordBound

theorem C63_4length : C63_4.length = 8 := by rfl

def C63_5 : List Column := [⟨40, [112,112,36,52,48], (some (15)), false, false, false⟩,⟨41, [112,112,36,52,49], (some (2)), false, false, false⟩,⟨42, [112,112,36,52,50], (some (15)), false, false, false⟩,⟨43, [112,112,36,52,51], (some (2)), false, false, false⟩,⟨44, [112,112,36,52,52], (some (4)), false, false, false⟩,⟨45, [109,36,52,53], (some (1)), false, false, false⟩,⟨46, [109,36,52,54], (some (14)), false, false, false⟩,⟨47, [99,36,52,55], (some (2)), false, false, false⟩]

def C63_5p0 : List Nat := [40,5,112,112,36,52,48,1,15,0,0,0,0,0,0,41,5,112,112,36,52,49,1,2,0,0,0,0,0,0,42,5,112,112,36,52,50,1,15,0,0,0,0,0,0,43,5,112,112,36,52,51,1,2,0,0,0,0,0,0,44,5,112,112,36,52,52,1,4,0,0,0,0,0,0,45,4,109,36,52,53,1,1,0,0,0,0,0,0,46,4,109,36,52,54,1,14,0,0,0,0,0,0,47,4,99,36,52,55,1,2,0,0,0,0,0,0]
theorem C63_5p0bound : C63_5p0.all wordBound = true := (by decide : [40,5,112,112,36,52,48,1,15,0,0,0,0,0,0,41,5,112,112,36,52,49,1,2,0,0,0,0,0,0,42,5,112,112,36,52,50,1,15,0,0,0,0,0,0,43,5,112,112,36,52,51,1,2,0,0,0,0,0,0,44,5,112,112,36,52,52,1,4,0,0,0,0,0,0,45,4,109,36,52,53,1,1,0,0,0,0,0,0,46,4,109,36,52,54,1,14,0,0,0,0,0,0,47,4,99,36,52,55,1,2,0,0,0,0,0,0].all wordBound = true)

def C63_5words : List Nat := C63_5p0

theorem C63_5wire : C63_5.flatMap columnWords = C63_5words := by
  rfl

theorem C63_5wordBound : C63_5words.all wordBound = true := by
  simp only [C63_5words,List.all_append,C63_5p0bound]
  try rfl

theorem C63_5bounded : ∀ n ∈ C63_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C63_5wordBound

theorem C63_5length : C63_5.length = 8 := by rfl

def C63_6 : List Column := [⟨48, [109,36,52,56], (some (2)), false, false, false⟩,⟨49, [99,36,52,57], (some (1)), false, false, false⟩,⟨50, [99,36,53,48], (some (1)), false, false, false⟩,⟨51, [36,114,101,116], (some (1)), false, false, false⟩,⟨52, [40,105,110,118,32,40,43,32,100,105,118,77,111,100,95,51,50,95,117,117,58,98,39,49,32,100,105,118,77,111,100,95,51,50,95,117,117,58,98,39,48,41,41], none, false, false, true⟩]

def C63_6p0 : List Nat := [48,4,109,36,52,56,1,2,0,0,0,0,0,0,49,4,99,36,52,57,1,1,0,0,0,0,0,0,50,4,99,36,53,48,1,1,0,0,0,0,0,0,51,4,36,114,101,116,1,1,0,0,0,0,0,0,52,43,40,105,110,118,32,40,43,32,100,105,118,77,111,100,95,51,50,95,117,117,58,98,39,49,32,100,105,118,77,111,100,95,51,50,95,117,117,58,98,39,48,41,41,0,0,0,0,0,0,1,0]
theorem C63_6p0bound : C63_6p0.all wordBound = true := (by decide : [48,4,109,36,52,56,1,2,0,0,0,0,0,0,49,4,99,36,52,57,1,1,0,0,0,0,0,0,50,4,99,36,53,48,1,1,0,0,0,0,0,0,51,4,36,114,101,116,1,1,0,0,0,0,0,0,52,43,40,105,110,118,32,40,43,32,100,105,118,77,111,100,95,51,50,95,117,117,58,98,39,49,32,100,105,118,77,111,100,95,51,50,95,117,117,58,98,39,48,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C63_6words : List Nat := C63_6p0

theorem C63_6wire : C63_6.flatMap columnWords = C63_6words := by
  rfl

theorem C63_6wordBound : C63_6words.all wordBound = true := by
  simp only [C63_6words,List.all_append,C63_6p0bound]
  try rfl

theorem C63_6bounded : ∀ n ∈ C63_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C63_6wordBound

theorem C63_6length : C63_6.length = 5 := by rfl

def M63 : Module := ⟨63, [100,105,118,77,111,100,95,51,50,95,117,117], false, false, C63_0 ++ C63_1 ++ C63_2 ++ C63_3 ++ C63_4 ++ C63_5 ++ C63_6, ((List.range 0).map (fun n => [n]))⟩

def M63prefix : List Nat := [63,12,100,105,118,77,111,100,95,51,50,95,117,117,0,0,0,0,53]
theorem M63prefixwordBound : M63prefix.all wordBound = true := by decide

def M63words : List Nat := M63prefix ++ C63_0words ++ C63_1words ++ C63_2words ++ C63_3words ++ C63_4words ++ C63_5words ++ C63_6words ++ [0]

theorem M63wire : module.encode M63 = M63words := by
  rw [module_fast]
  simp only [M63,moduleWords,List.length_append,List.flatMap_append,C63_0length,C63_1length,C63_2length,C63_3length,C63_4length,C63_5length,C63_6length,C63_0wire,C63_1wire,C63_2wire,C63_3wire,C63_4wire,C63_5wire,C63_6wire]
  rfl

theorem M63wordBound : M63words.all wordBound = true := by
  simp only [M63words,List.all_append,M63prefixwordBound,C63_0wordBound,C63_1wordBound,C63_2wordBound,C63_3wordBound,C63_4wordBound,C63_5wordBound,C63_6wordBound]
  decide

theorem M63bounded : ∀ n ∈ M63words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M63wordBound

end DivRemFV.Replay
