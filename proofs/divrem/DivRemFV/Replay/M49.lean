import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C49_0 : List Column := [⟨0, [114,97,109,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨1, [114,97,109,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨2, [114,97,109,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨3, [97,100,100,114,101,115,115,39,51], (some (16)), true, false, false⟩,⟨4, [97,100,100,114,101,115,115,39,50], (some (16)), true, false, false⟩,⟨5, [97,100,100,114,101,115,115,39,49], (some (16)), true, false, false⟩,⟨6, [97,100,100,114,101,115,115,39,48], (some (16)), true, false, false⟩,⟨7, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,50], (some (16)), false, true, false⟩]

def C49_0p0 : List Nat := [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115]
theorem C49_0p0bound : C49_0p0.all wordBound = true := (by decide : [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115].all wordBound = true)

def C49_0p1 : List Nat := [115,39,48,1,16,1,0,0,0,0,0,7,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0]
theorem C49_0p1bound : C49_0p1.all wordBound = true := (by decide : [115,39,48,1,16,1,0,0,0,0,0,7,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0].all wordBound = true)

def C49_0words : List Nat := C49_0p0 ++ C49_0p1

theorem C49_0wire : C49_0.flatMap columnWords = C49_0words := by
  rfl

theorem C49_0wordBound : C49_0words.all wordBound = true := by
  simp only [C49_0words,List.all_append,C49_0p0bound,C49_0p1bound]
  try rfl

theorem C49_0bounded : ∀ n ∈ C49_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C49_0wordBound

theorem C49_0length : C49_0.length = 8 := by rfl

def C49_1 : List Column := [⟨8, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨9, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨10, [118,97,108,117,101,39,49], (some (16)), false, true, false⟩,⟨11, [118,97,108,117,101,39,48], (some (16)), false, true, false⟩,⟨12, [98,111,102,102,115,101,116], (some (2)), false, false, false⟩,⟨13, [119,111,102,102,115,101,116,39,51], (some (14)), false, false, false⟩,⟨14, [119,111,102,102,115,101,116,39,50], (some (16)), false, false, false⟩,⟨15, [119,111,102,102,115,101,116,39,49], (some (16)), false, false, false⟩]

def C49_1p0 : List Nat := [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,10,7,118,97,108,117,101,39,49,1,16,0,0,1,0,0,0,11,7,118,97,108,117,101,39,48,1,16,0,0,1,0,0,0,12,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0,14,9,119,111,102,102,115,101]
theorem C49_1p0bound : C49_1p0.all wordBound = true := (by decide : [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,10,7,118,97,108,117,101,39,49,1,16,0,0,1,0,0,0,11,7,118,97,108,117,101,39,48,1,16,0,0,1,0,0,0,12,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0,14,9,119,111,102,102,115,101].all wordBound = true)

def C49_1p1 : List Nat := [116,39,50,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0]
theorem C49_1p1bound : C49_1p1.all wordBound = true := (by decide : [116,39,50,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C49_1words : List Nat := C49_1p0 ++ C49_1p1

theorem C49_1wire : C49_1.flatMap columnWords = C49_1words := by
  rfl

theorem C49_1wordBound : C49_1words.all wordBound = true := by
  simp only [C49_1words,List.all_append,C49_1p0bound,C49_1p1bound]
  try rfl

theorem C49_1bounded : ∀ n ∈ C49_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C49_1wordBound

theorem C49_1length : C49_1.length = 8 := by rfl

def C49_2 : List Column := [⟨16, [119,111,102,102,115,101,116,39,48], (some (16)), false, false, false⟩,⟨17, [116,114,97,115,104,39,49], (some (16)), false, false, false⟩,⟨18, [116,114,97,115,104,39,48], (some (16)), false, false, false⟩,⟨19, [115,104,105,102,116], (some (5)), false, false, false⟩,⟨20, [100,119,39,51], (some (16)), false, false, false⟩,⟨21, [100,119,39,50], (some (16)), false, false, false⟩,⟨22, [100,119,39,49], (some (16)), false, false, false⟩,⟨23, [100,119,39,48], (some (16)), false, false, false⟩]

def C49_2p0 : List Nat := [16,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0,17,7,116,114,97,115,104,39,49,1,16,0,0,0,0,0,0,18,7,116,114,97,115,104,39,48,1,16,0,0,0,0,0,0,19,5,115,104,105,102,116,1,5,0,0,0,0,0,0,20,4,100,119,39,51,1,16,0,0,0,0,0,0,21,4,100,119,39,50,1,16,0,0,0,0,0,0,22,4,100,119,39,49,1,16,0,0,0,0,0,0,23,4,100,119,39,48,1,16,0,0,0,0,0,0]
theorem C49_2p0bound : C49_2p0.all wordBound = true := (by decide : [16,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0,17,7,116,114,97,115,104,39,49,1,16,0,0,0,0,0,0,18,7,116,114,97,115,104,39,48,1,16,0,0,0,0,0,0,19,5,115,104,105,102,116,1,5,0,0,0,0,0,0,20,4,100,119,39,51,1,16,0,0,0,0,0,0,21,4,100,119,39,50,1,16,0,0,0,0,0,0,22,4,100,119,39,49,1,16,0,0,0,0,0,0,23,4,100,119,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C49_2words : List Nat := C49_2p0

theorem C49_2wire : C49_2.flatMap columnWords = C49_2words := by
  rfl

theorem C49_2wordBound : C49_2words.all wordBound = true := by
  simp only [C49_2words,List.all_append,C49_2p0bound]
  try rfl

theorem C49_2bounded : ∀ n ∈ C49_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C49_2wordBound

theorem C49_2length : C49_2.length = 8 := by rfl

def C49_3 : List Column := [⟨24, [36,55,39,49], (some (16)), false, false, false⟩,⟨25, [36,55,39,48], (some (16)), false, false, false⟩,⟨26, [36,56,39,51], (some (16)), false, false, false⟩,⟨27, [36,56,39,50], (some (16)), false, false, false⟩,⟨28, [36,56,39,49], (some (16)), false, false, false⟩,⟨29, [36,56,39,48], (some (16)), false, false, false⟩,⟨30, [36,57,39,49], (some (16)), false, false, false⟩,⟨31, [36,57,39,48], (some (16)), false, false, false⟩]

def C49_3p0 : List Nat := [24,4,36,55,39,49,1,16,0,0,0,0,0,0,25,4,36,55,39,48,1,16,0,0,0,0,0,0,26,4,36,56,39,51,1,16,0,0,0,0,0,0,27,4,36,56,39,50,1,16,0,0,0,0,0,0,28,4,36,56,39,49,1,16,0,0,0,0,0,0,29,4,36,56,39,48,1,16,0,0,0,0,0,0,30,4,36,57,39,49,1,16,0,0,0,0,0,0,31,4,36,57,39,48,1,16,0,0,0,0,0,0]
theorem C49_3p0bound : C49_3p0.all wordBound = true := (by decide : [24,4,36,55,39,49,1,16,0,0,0,0,0,0,25,4,36,55,39,48,1,16,0,0,0,0,0,0,26,4,36,56,39,51,1,16,0,0,0,0,0,0,27,4,36,56,39,50,1,16,0,0,0,0,0,0,28,4,36,56,39,49,1,16,0,0,0,0,0,0,29,4,36,56,39,48,1,16,0,0,0,0,0,0,30,4,36,57,39,49,1,16,0,0,0,0,0,0,31,4,36,57,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C49_3words : List Nat := C49_3p0

theorem C49_3wire : C49_3.flatMap columnWords = C49_3words := by
  rfl

theorem C49_3wordBound : C49_3words.all wordBound = true := by
  simp only [C49_3words,List.all_append,C49_3p0bound]
  try rfl

theorem C49_3bounded : ∀ n ∈ C49_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C49_3wordBound

theorem C49_3length : C49_3.length = 8 := by rfl

def C49_4 : List Column := [⟨32, [36,49,48], (some (2)), false, false, false⟩,⟨33, [36,49,49,39,51], (some (16)), false, false, false⟩,⟨34, [36,49,49,39,50], (some (16)), false, false, false⟩,⟨35, [36,49,49,39,49], (some (16)), false, false, false⟩,⟨36, [36,49,49,39,48], (some (16)), false, false, false⟩,⟨37, [114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,51], (some (16)), false, false, false⟩,⟨38, [114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,50], (some (16)), false, false, false⟩,⟨39, [114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,49], (some (16)), false, false, false⟩]

def C49_4p0 : List Nat := [32,3,36,49,48,1,2,0,0,0,0,0,0,33,5,36,49,49,39,51,1,16,0,0,0,0,0,0,34,5,36,49,49,39,50,1,16,0,0,0,0,0,0,35,5,36,49,49,39,49,1,16,0,0,0,0,0,0,36,5,36,49,49,39,48,1,16,0,0,0,0,0,0,37,16,114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,51,1,16,0,0,0,0,0,0,38,16,114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,50,1,16,0,0,0,0,0,0,39,16,114]
theorem C49_4p0bound : C49_4p0.all wordBound = true := (by decide : [32,3,36,49,48,1,2,0,0,0,0,0,0,33,5,36,49,49,39,51,1,16,0,0,0,0,0,0,34,5,36,49,49,39,50,1,16,0,0,0,0,0,0,35,5,36,49,49,39,49,1,16,0,0,0,0,0,0,36,5,36,49,49,39,48,1,16,0,0,0,0,0,0,37,16,114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,51,1,16,0,0,0,0,0,0,38,16,114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,50,1,16,0,0,0,0,0,0,39,16,114].all wordBound = true)

def C49_4p1 : List Nat := [97,119,95,115,104,108,95,114,101,115,36,49,50,39,49,1,16,0,0,0,0,0,0]
theorem C49_4p1bound : C49_4p1.all wordBound = true := (by decide : [97,119,95,115,104,108,95,114,101,115,36,49,50,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C49_4words : List Nat := C49_4p0 ++ C49_4p1

theorem C49_4wire : C49_4.flatMap columnWords = C49_4words := by
  rfl

theorem C49_4wordBound : C49_4words.all wordBound = true := by
  simp only [C49_4words,List.all_append,C49_4p0bound,C49_4p1bound]
  try rfl

theorem C49_4bounded : ∀ n ∈ C49_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C49_4wordBound

theorem C49_4length : C49_4.length = 8 := by rfl

def C49_5 : List Column := [⟨40, [114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,48], (some (16)), false, false, false⟩,⟨41, [115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,51], (some (11)), false, false, false⟩,⟨42, [115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,50], (some (16)), false, false, false⟩,⟨43, [115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,49], (some (16)), false, false, false⟩,⟨44, [115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,48], (some (16)), false, false, false⟩,⟨45, [115,116,97,109,112,36,49,54,39,50], (some (16)), false, false, false⟩,⟨46, [115,116,97,109,112,36,49,54,39,49], (some (16)), false, false, false⟩,⟨47, [115,116,97,109,112,36,49,54,39,48], (some (16)), false, false, false⟩]

def C49_5p0 : List Nat := [40,16,114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,48,1,16,0,0,0,0,0,0,41,17,115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,51,1,11,0,0,0,0,0,0,42,17,115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,50,1,16,0,0,0,0,0,0,43,17,115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,49,1,16,0,0,0,0,0,0,44,17,115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,48,1,16]
theorem C49_5p0bound : C49_5p0.all wordBound = true := (by decide : [40,16,114,97,119,95,115,104,108,95,114,101,115,36,49,50,39,48,1,16,0,0,0,0,0,0,41,17,115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,51,1,11,0,0,0,0,0,0,42,17,115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,50,1,16,0,0,0,0,0,0,43,17,115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,49,1,16,0,0,0,0,0,0,44,17,115,104,108,95,114,101,115,95,104,105,103,104,36,49,51,39,48,1,16].all wordBound = true)

def C49_5p1 : List Nat := [0,0,0,0,0,0,45,10,115,116,97,109,112,36,49,54,39,50,1,16,0,0,0,0,0,0,46,10,115,116,97,109,112,36,49,54,39,49,1,16,0,0,0,0,0,0,47,10,115,116,97,109,112,36,49,54,39,48,1,16,0,0,0,0,0,0]
theorem C49_5p1bound : C49_5p1.all wordBound = true := (by decide : [0,0,0,0,0,0,45,10,115,116,97,109,112,36,49,54,39,50,1,16,0,0,0,0,0,0,46,10,115,116,97,109,112,36,49,54,39,49,1,16,0,0,0,0,0,0,47,10,115,116,97,109,112,36,49,54,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C49_5words : List Nat := C49_5p0 ++ C49_5p1

theorem C49_5wire : C49_5.flatMap columnWords = C49_5words := by
  rfl

theorem C49_5wordBound : C49_5words.all wordBound = true := by
  simp only [C49_5words,List.all_append,C49_5p0bound,C49_5p1bound]
  try rfl

theorem C49_5bounded : ∀ n ∈ C49_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C49_5wordBound

theorem C49_5length : C49_5.length = 8 := by rfl

def C49_6 : List Column := [⟨48, [102,115,99,36,49,55], (some (1)), false, false, false⟩,⟨49, [99,36,52,57], (some (14)), false, false, false⟩,⟨50, [99,36,53,48], (some (14)), false, false, false⟩,⟨51, [99,36,53,49], (some (14)), false, false, false⟩,⟨52, [99,36,53,50], (some (14)), false, false, false⟩,⟨53, [99,36,53,51], (some (1)), false, false, false⟩,⟨54, [99,36,53,52], (some (1)), false, false, false⟩,⟨55, [99,36,53,55], (some (1)), false, false, false⟩]

def C49_6p0 : List Nat := [48,6,102,115,99,36,49,55,1,1,0,0,0,0,0,0,49,4,99,36,52,57,1,14,0,0,0,0,0,0,50,4,99,36,53,48,1,14,0,0,0,0,0,0,51,4,99,36,53,49,1,14,0,0,0,0,0,0,52,4,99,36,53,50,1,14,0,0,0,0,0,0,53,4,99,36,53,51,1,1,0,0,0,0,0,0,54,4,99,36,53,52,1,1,0,0,0,0,0,0,55,4,99,36,53,55,1,1,0,0,0,0,0,0]
theorem C49_6p0bound : C49_6p0.all wordBound = true := (by decide : [48,6,102,115,99,36,49,55,1,1,0,0,0,0,0,0,49,4,99,36,52,57,1,14,0,0,0,0,0,0,50,4,99,36,53,48,1,14,0,0,0,0,0,0,51,4,99,36,53,49,1,14,0,0,0,0,0,0,52,4,99,36,53,50,1,14,0,0,0,0,0,0,53,4,99,36,53,51,1,1,0,0,0,0,0,0,54,4,99,36,53,52,1,1,0,0,0,0,0,0,55,4,99,36,53,55,1,1,0,0,0,0,0,0].all wordBound = true)

def C49_6words : List Nat := C49_6p0

theorem C49_6wire : C49_6.flatMap columnWords = C49_6words := by
  rfl

theorem C49_6wordBound : C49_6words.all wordBound = true := by
  simp only [C49_6words,List.all_append,C49_6p0bound]
  try rfl

theorem C49_6bounded : ∀ n ∈ C49_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C49_6wordBound

theorem C49_6length : C49_6.length = 8 := by rfl

def C49_7 : List Column := [⟨56, [99,36,53,56], (some (1)), false, false, false⟩,⟨57, [99,36,53,57], (some (1)), false, false, false⟩,⟨58, [36,99,115,116,95,48], (some (0)), false, false, false⟩,⟨59, [116,36,54,49], (some (11)), false, false, false⟩,⟨60, [116,36,54,50], (some (5)), false, false, false⟩,⟨61, [116,36,54,51], (some (11)), false, false, false⟩,⟨62, [116,36,54,52], (some (5)), false, false, false⟩,⟨63, [116,36,54,53], (some (11)), false, false, false⟩]

def C49_7p0 : List Nat := [56,4,99,36,53,56,1,1,0,0,0,0,0,0,57,4,99,36,53,57,1,1,0,0,0,0,0,0,58,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,59,4,116,36,54,49,1,11,0,0,0,0,0,0,60,4,116,36,54,50,1,5,0,0,0,0,0,0,61,4,116,36,54,51,1,11,0,0,0,0,0,0,62,4,116,36,54,52,1,5,0,0,0,0,0,0,63,4,116,36,54,53,1,11,0,0,0,0,0,0]
theorem C49_7p0bound : C49_7p0.all wordBound = true := (by decide : [56,4,99,36,53,56,1,1,0,0,0,0,0,0,57,4,99,36,53,57,1,1,0,0,0,0,0,0,58,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,59,4,116,36,54,49,1,11,0,0,0,0,0,0,60,4,116,36,54,50,1,5,0,0,0,0,0,0,61,4,116,36,54,51,1,11,0,0,0,0,0,0,62,4,116,36,54,52,1,5,0,0,0,0,0,0,63,4,116,36,54,53,1,11,0,0,0,0,0,0].all wordBound = true)

def C49_7words : List Nat := C49_7p0

theorem C49_7wire : C49_7.flatMap columnWords = C49_7words := by
  rfl

theorem C49_7wordBound : C49_7words.all wordBound = true := by
  simp only [C49_7words,List.all_append,C49_7p0bound]
  try rfl

theorem C49_7bounded : ∀ n ∈ C49_7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C49_7wordBound

theorem C49_7length : C49_7.length = 8 := by rfl

def C49_8 : List Column := [⟨64, [116,36,54,54], (some (5)), false, false, false⟩,⟨65, [99,36,54,55], (some (1)), false, false, false⟩,⟨66, [99,36,54,56], (some (1)), false, false, false⟩,⟨67, [36,114,101,116], (some (1)), false, false, false⟩,⟨68, [36,108,111,111,107,117,112,95,115,101,108,95,54,56], (some (1)), false, false, false⟩,⟨69, [36,108,111,111,107,117,112,95,115,101,108,95,54,57], (some (1)), false, false, false⟩,⟨70, [40,105,110,118,32,114,101,97,100,95,51,50,58,98,111,102,102,115,101,116,41], none, false, false, true⟩]

def C49_8p0 : List Nat := [64,4,116,36,54,54,1,5,0,0,0,0,0,0,65,4,99,36,54,55,1,1,0,0,0,0,0,0,66,4,99,36,54,56,1,1,0,0,0,0,0,0,67,4,36,114,101,116,1,1,0,0,0,0,0,0,68,14,36,108,111,111,107,117,112,95,115,101,108,95,54,56,1,1,0,0,0,0,0,0,69,14,36,108,111,111,107,117,112,95,115,101,108,95,54,57,1,1,0,0,0,0,0,0,70,21,40,105,110,118,32,114,101,97,100,95,51,50,58,98,111,102,102,115,101,116,41,0]
theorem C49_8p0bound : C49_8p0.all wordBound = true := (by decide : [64,4,116,36,54,54,1,5,0,0,0,0,0,0,65,4,99,36,54,55,1,1,0,0,0,0,0,0,66,4,99,36,54,56,1,1,0,0,0,0,0,0,67,4,36,114,101,116,1,1,0,0,0,0,0,0,68,14,36,108,111,111,107,117,112,95,115,101,108,95,54,56,1,1,0,0,0,0,0,0,69,14,36,108,111,111,107,117,112,95,115,101,108,95,54,57,1,1,0,0,0,0,0,0,70,21,40,105,110,118,32,114,101,97,100,95,51,50,58,98,111,102,102,115,101,116,41,0].all wordBound = true)

def C49_8p1 : List Nat := [0,0,0,0,0,1,0]
theorem C49_8p1bound : C49_8p1.all wordBound = true := (by decide : [0,0,0,0,0,1,0].all wordBound = true)

def C49_8words : List Nat := C49_8p0 ++ C49_8p1

theorem C49_8wire : C49_8.flatMap columnWords = C49_8words := by
  rfl

theorem C49_8wordBound : C49_8words.all wordBound = true := by
  simp only [C49_8words,List.all_append,C49_8p0bound,C49_8p1bound]
  try rfl

theorem C49_8bounded : ∀ n ∈ C49_8words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C49_8wordBound

theorem C49_8length : C49_8.length = 7 := by rfl

def M49 : Module := ⟨49, [114,101,97,100,95,51,50], false, false, C49_0 ++ C49_1 ++ C49_2 ++ C49_3 ++ C49_4 ++ C49_5 ++ C49_6 ++ C49_7 ++ C49_8, ((List.range 0).map (fun n => [n]))⟩

def M49prefix : List Nat := [49,7,114,101,97,100,95,51,50,0,0,0,0,71]
theorem M49prefixwordBound : M49prefix.all wordBound = true := by decide

def M49words : List Nat := M49prefix ++ C49_0words ++ C49_1words ++ C49_2words ++ C49_3words ++ C49_4words ++ C49_5words ++ C49_6words ++ C49_7words ++ C49_8words ++ [0]

theorem M49wire : module.encode M49 = M49words := by
  rw [module_fast]
  simp only [M49,moduleWords,List.length_append,List.flatMap_append,C49_0length,C49_1length,C49_2length,C49_3length,C49_4length,C49_5length,C49_6length,C49_7length,C49_8length,C49_0wire,C49_1wire,C49_2wire,C49_3wire,C49_4wire,C49_5wire,C49_6wire,C49_7wire,C49_8wire]
  rfl

theorem M49wordBound : M49words.all wordBound = true := by
  simp only [M49words,List.all_append,M49prefixwordBound,C49_0wordBound,C49_1wordBound,C49_2wordBound,C49_3wordBound,C49_4wordBound,C49_5wordBound,C49_6wordBound,C49_7wordBound,C49_8wordBound]
  decide

theorem M49bounded : ∀ n ∈ M49words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M49wordBound

end DivRemFV.Replay
