import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C48_0 : List Column := [⟨0, [114,97,109,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨1, [114,97,109,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨2, [114,97,109,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨3, [97,100,100,114,101,115,115,39,51], (some (16)), true, false, false⟩,⟨4, [97,100,100,114,101,115,115,39,50], (some (16)), true, false, false⟩,⟨5, [97,100,100,114,101,115,115,39,49], (some (16)), true, false, false⟩,⟨6, [97,100,100,114,101,115,115,39,48], (some (16)), true, false, false⟩,⟨7, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,50], (some (16)), false, true, false⟩]

def C48_0p0 : List Nat := [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115]
theorem C48_0p0bound : C48_0p0.all wordBound = true := (by decide : [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115].all wordBound = true)

def C48_0p1 : List Nat := [115,39,48,1,16,1,0,0,0,0,0,7,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0]
theorem C48_0p1bound : C48_0p1.all wordBound = true := (by decide : [115,39,48,1,16,1,0,0,0,0,0,7,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0].all wordBound = true)

def C48_0words : List Nat := C48_0p0 ++ C48_0p1

theorem C48_0wire : C48_0.flatMap columnWords = C48_0words := by
  rfl

theorem C48_0wordBound : C48_0words.all wordBound = true := by
  simp only [C48_0words,List.all_append,C48_0p0bound,C48_0p1bound]
  try rfl

theorem C48_0bounded : ∀ n ∈ C48_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C48_0wordBound

theorem C48_0length : C48_0.length = 8 := by rfl

def C48_1 : List Column := [⟨8, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨9, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨10, [118,97,108,117,101], (some (16)), false, true, false⟩,⟨11, [98,111,102,102,115,101,116], (some (2)), false, false, false⟩,⟨12, [119,111,102,102,115,101,116,39,51], (some (14)), false, false, false⟩,⟨13, [119,111,102,102,115,101,116,39,50], (some (16)), false, false, false⟩,⟨14, [119,111,102,102,115,101,116,39,49], (some (16)), false, false, false⟩,⟨15, [119,111,102,102,115,101,116,39,48], (some (16)), false, false, false⟩]

def C48_1p0 : List Nat := [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,10,5,118,97,108,117,101,1,16,0,0,1,0,0,0,11,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,12,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0,0,0,14,9,119,111,102,102,115,101]
theorem C48_1p0bound : C48_1p0.all wordBound = true := (by decide : [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,10,5,118,97,108,117,101,1,16,0,0,1,0,0,0,11,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,12,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0,0,0,14,9,119,111,102,102,115,101].all wordBound = true)

def C48_1p1 : List Nat := [116,39,49,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0]
theorem C48_1p1bound : C48_1p1.all wordBound = true := (by decide : [116,39,49,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C48_1words : List Nat := C48_1p0 ++ C48_1p1

theorem C48_1wire : C48_1.flatMap columnWords = C48_1words := by
  rfl

theorem C48_1wordBound : C48_1words.all wordBound = true := by
  simp only [C48_1words,List.all_append,C48_1p0bound,C48_1p1bound]
  try rfl

theorem C48_1bounded : ∀ n ∈ C48_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C48_1wordBound

theorem C48_1length : C48_1.length = 8 := by rfl

def C48_2 : List Column := [⟨16, [116,109,112,49,54], (some (16)), false, false, false⟩,⟨17, [108,111,39,49], (some (16)), false, false, false⟩,⟨18, [108,111,39,48], (some (16)), false, false, false⟩,⟨19, [116,109,112,51,50,39,49], (some (16)), false, false, false⟩,⟨20, [116,109,112,51,50,39,48], (some (16)), false, false, false⟩,⟨21, [104,105,39,49], (some (16)), false, false, false⟩,⟨22, [104,105,39,48], (some (16)), false, false, false⟩,⟨23, [36,57], (some (4)), false, false, false⟩]

def C48_2p0 : List Nat := [16,5,116,109,112,49,54,1,16,0,0,0,0,0,0,17,4,108,111,39,49,1,16,0,0,0,0,0,0,18,4,108,111,39,48,1,16,0,0,0,0,0,0,19,7,116,109,112,51,50,39,49,1,16,0,0,0,0,0,0,20,7,116,109,112,51,50,39,48,1,16,0,0,0,0,0,0,21,4,104,105,39,49,1,16,0,0,0,0,0,0,22,4,104,105,39,48,1,16,0,0,0,0,0,0,23,2,36,57,1,4,0,0,0,0,0,0]
theorem C48_2p0bound : C48_2p0.all wordBound = true := (by decide : [16,5,116,109,112,49,54,1,16,0,0,0,0,0,0,17,4,108,111,39,49,1,16,0,0,0,0,0,0,18,4,108,111,39,48,1,16,0,0,0,0,0,0,19,7,116,109,112,51,50,39,49,1,16,0,0,0,0,0,0,20,7,116,109,112,51,50,39,48,1,16,0,0,0,0,0,0,21,4,104,105,39,49,1,16,0,0,0,0,0,0,22,4,104,105,39,48,1,16,0,0,0,0,0,0,23,2,36,57,1,4,0,0,0,0,0,0].all wordBound = true)

def C48_2words : List Nat := C48_2p0

theorem C48_2wire : C48_2.flatMap columnWords = C48_2words := by
  rfl

theorem C48_2wordBound : C48_2words.all wordBound = true := by
  simp only [C48_2words,List.all_append,C48_2p0bound]
  try rfl

theorem C48_2bounded : ∀ n ∈ C48_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C48_2wordBound

theorem C48_2length : C48_2.length = 8 := by rfl

def C48_3 : List Column := [⟨24, [36,49,49], (some (5)), false, false, false⟩,⟨25, [36,49,50,39,51], (some (16)), false, false, false⟩,⟨26, [36,49,50,39,50], (some (16)), false, false, false⟩,⟨27, [36,49,50,39,49], (some (16)), false, false, false⟩,⟨28, [36,49,50,39,48], (some (16)), false, false, false⟩,⟨29, [36,49,51,39,51], (some (16)), false, false, false⟩,⟨30, [36,49,51,39,50], (some (16)), false, false, false⟩,⟨31, [36,49,51,39,49], (some (16)), false, false, false⟩]

def C48_3p0 : List Nat := [24,3,36,49,49,1,5,0,0,0,0,0,0,25,5,36,49,50,39,51,1,16,0,0,0,0,0,0,26,5,36,49,50,39,50,1,16,0,0,0,0,0,0,27,5,36,49,50,39,49,1,16,0,0,0,0,0,0,28,5,36,49,50,39,48,1,16,0,0,0,0,0,0,29,5,36,49,51,39,51,1,16,0,0,0,0,0,0,30,5,36,49,51,39,50,1,16,0,0,0,0,0,0,31,5,36,49,51,39,49,1,16,0,0,0,0,0,0]
theorem C48_3p0bound : C48_3p0.all wordBound = true := (by decide : [24,3,36,49,49,1,5,0,0,0,0,0,0,25,5,36,49,50,39,51,1,16,0,0,0,0,0,0,26,5,36,49,50,39,50,1,16,0,0,0,0,0,0,27,5,36,49,50,39,49,1,16,0,0,0,0,0,0,28,5,36,49,50,39,48,1,16,0,0,0,0,0,0,29,5,36,49,51,39,51,1,16,0,0,0,0,0,0,30,5,36,49,51,39,50,1,16,0,0,0,0,0,0,31,5,36,49,51,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C48_3words : List Nat := C48_3p0

theorem C48_3wire : C48_3.flatMap columnWords = C48_3words := by
  rfl

theorem C48_3wordBound : C48_3words.all wordBound = true := by
  simp only [C48_3words,List.all_append,C48_3p0bound]
  try rfl

theorem C48_3bounded : ∀ n ∈ C48_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C48_3wordBound

theorem C48_3length : C48_3.length = 8 := by rfl

def C48_4 : List Column := [⟨32, [36,49,51,39,48], (some (16)), false, false, false⟩,⟨33, [36,49,52,39,51], (some (16)), false, false, false⟩,⟨34, [36,49,52,39,50], (some (16)), false, false, false⟩,⟨35, [36,49,52,39,49], (some (16)), false, false, false⟩,⟨36, [36,49,52,39,48], (some (16)), false, false, false⟩,⟨37, [115,116,97,109,112,36,49,56,39,50], (some (16)), false, false, false⟩,⟨38, [115,116,97,109,112,36,49,56,39,49], (some (16)), false, false, false⟩,⟨39, [115,116,97,109,112,36,49,56,39,48], (some (16)), false, false, false⟩]

def C48_4p0 : List Nat := [32,5,36,49,51,39,48,1,16,0,0,0,0,0,0,33,5,36,49,52,39,51,1,16,0,0,0,0,0,0,34,5,36,49,52,39,50,1,16,0,0,0,0,0,0,35,5,36,49,52,39,49,1,16,0,0,0,0,0,0,36,5,36,49,52,39,48,1,16,0,0,0,0,0,0,37,10,115,116,97,109,112,36,49,56,39,50,1,16,0,0,0,0,0,0,38,10,115,116,97,109,112,36,49,56,39,49,1,16,0,0,0,0,0,0,39,10,115,116,97,109,112,36,49,56,39,48,1]
theorem C48_4p0bound : C48_4p0.all wordBound = true := (by decide : [32,5,36,49,51,39,48,1,16,0,0,0,0,0,0,33,5,36,49,52,39,51,1,16,0,0,0,0,0,0,34,5,36,49,52,39,50,1,16,0,0,0,0,0,0,35,5,36,49,52,39,49,1,16,0,0,0,0,0,0,36,5,36,49,52,39,48,1,16,0,0,0,0,0,0,37,10,115,116,97,109,112,36,49,56,39,50,1,16,0,0,0,0,0,0,38,10,115,116,97,109,112,36,49,56,39,49,1,16,0,0,0,0,0,0,39,10,115,116,97,109,112,36,49,56,39,48,1].all wordBound = true)

def C48_4p1 : List Nat := [16,0,0,0,0,0,0]
theorem C48_4p1bound : C48_4p1.all wordBound = true := (by decide : [16,0,0,0,0,0,0].all wordBound = true)

def C48_4words : List Nat := C48_4p0 ++ C48_4p1

theorem C48_4wire : C48_4.flatMap columnWords = C48_4words := by
  rfl

theorem C48_4wordBound : C48_4words.all wordBound = true := by
  simp only [C48_4words,List.all_append,C48_4p0bound,C48_4p1bound]
  try rfl

theorem C48_4bounded : ∀ n ∈ C48_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C48_4wordBound

theorem C48_4length : C48_4.length = 8 := by rfl

def C48_5 : List Column := [⟨40, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,49], (some (1)), false, false, false⟩,⟨41, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,50], (some (1)), false, false, false⟩,⟨42, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,51], (some (1)), false, false, false⟩,⟨43, [108,115,119,36,50,50], (some (1)), false, false, false⟩,⟨44, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,100,101,102,97,117,108,116], (some (1)), false, false, false⟩,⟨45, [99,36,53,48], (some (14)), false, false, false⟩,⟨46, [99,36,53,49], (some (14)), false, false, false⟩,⟨47, [99,36,53,50], (some (14)), false, false, false⟩]

def C48_5p0 : List Nat := [40,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,49,1,1,0,0,0,0,0,0,41,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,50,1,1,0,0,0,0,0,0,42,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,51,1,1,0,0,0,0,0,0,43,6,108,115,119,36,50,50,1,1,0,0,0,0,0,0,44,24,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,100,101,102,97,117,108,116,1,1]
theorem C48_5p0bound : C48_5p0.all wordBound = true := (by decide : [40,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,49,1,1,0,0,0,0,0,0,41,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,50,1,1,0,0,0,0,0,0,42,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,51,1,1,0,0,0,0,0,0,43,6,108,115,119,36,50,50,1,1,0,0,0,0,0,0,44,24,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,100,101,102,97,117,108,116,1,1].all wordBound = true)

def C48_5p1 : List Nat := [0,0,0,0,0,0,45,4,99,36,53,48,1,14,0,0,0,0,0,0,46,4,99,36,53,49,1,14,0,0,0,0,0,0,47,4,99,36,53,50,1,14,0,0,0,0,0,0]
theorem C48_5p1bound : C48_5p1.all wordBound = true := (by decide : [0,0,0,0,0,0,45,4,99,36,53,48,1,14,0,0,0,0,0,0,46,4,99,36,53,49,1,14,0,0,0,0,0,0,47,4,99,36,53,50,1,14,0,0,0,0,0,0].all wordBound = true)

def C48_5words : List Nat := C48_5p0 ++ C48_5p1

theorem C48_5wire : C48_5.flatMap columnWords = C48_5words := by
  rfl

theorem C48_5wordBound : C48_5words.all wordBound = true := by
  simp only [C48_5words,List.all_append,C48_5p0bound,C48_5p1bound]
  try rfl

theorem C48_5bounded : ∀ n ∈ C48_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C48_5wordBound

theorem C48_5length : C48_5.length = 8 := by rfl

def C48_6 : List Column := [⟨48, [99,36,53,51], (some (14)), false, false, false⟩,⟨49, [99,36,53,52], (some (1)), false, false, false⟩,⟨50, [99,36,53,53], (some (1)), false, false, false⟩,⟨51, [99,36,53,54], (some (1)), false, false, false⟩,⟨52, [99,36,53,55], (some (1)), false, false, false⟩,⟨53, [99,36,53,56], (some (1)), false, false, false⟩,⟨54, [99,36,53,57], (some (1)), false, false, false⟩,⟨55, [99,36,54,48], (some (1)), false, false, false⟩]

def C48_6p0 : List Nat := [48,4,99,36,53,51,1,14,0,0,0,0,0,0,49,4,99,36,53,52,1,1,0,0,0,0,0,0,50,4,99,36,53,53,1,1,0,0,0,0,0,0,51,4,99,36,53,54,1,1,0,0,0,0,0,0,52,4,99,36,53,55,1,1,0,0,0,0,0,0,53,4,99,36,53,56,1,1,0,0,0,0,0,0,54,4,99,36,53,57,1,1,0,0,0,0,0,0,55,4,99,36,54,48,1,1,0,0,0,0,0,0]
theorem C48_6p0bound : C48_6p0.all wordBound = true := (by decide : [48,4,99,36,53,51,1,14,0,0,0,0,0,0,49,4,99,36,53,52,1,1,0,0,0,0,0,0,50,4,99,36,53,53,1,1,0,0,0,0,0,0,51,4,99,36,53,54,1,1,0,0,0,0,0,0,52,4,99,36,53,55,1,1,0,0,0,0,0,0,53,4,99,36,53,56,1,1,0,0,0,0,0,0,54,4,99,36,53,57,1,1,0,0,0,0,0,0,55,4,99,36,54,48,1,1,0,0,0,0,0,0].all wordBound = true)

def C48_6words : List Nat := C48_6p0

theorem C48_6wire : C48_6.flatMap columnWords = C48_6words := by
  rfl

theorem C48_6wordBound : C48_6words.all wordBound = true := by
  simp only [C48_6words,List.all_append,C48_6p0bound]
  try rfl

theorem C48_6bounded : ∀ n ∈ C48_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C48_6wordBound

theorem C48_6length : C48_6.length = 8 := by rfl

def C48_7 : List Column := [⟨56, [36,99,115,116,95,48], (some (0)), false, false, false⟩,⟨57, [36,114,101,116], (some (1)), false, false, false⟩,⟨58, [36,108,111,111,107,117,112,95,115,101,108,95,53,56], (some (1)), false, false, false⟩,⟨59, [36,108,111,111,107,117,112,95,115,101,108,95,53,57], (some (1)), false, false, false⟩,⟨60, [36,108,111,111,107,117,112,95,115,101,108,95,54,48], (some (1)), false, false, false⟩,⟨61, [40,105,110,118,32,114,101,97,100,95,49,54,58,98,111,102,102,115,101,116,41], none, false, false, true⟩,⟨62, [40,105,110,118,32,40,45,32,114,101,97,100,95,49,54,58,98,111,102,102,115,101,116,32,49,41,41], none, false, false, true⟩,⟨63, [40,105,110,118,32,40,45,32,114,101,97,100,95,49,54,58,98,111,102,102,115,101,116,32,50,41,41], none, false, false, true⟩]

def C48_7p0 : List Nat := [56,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,57,4,36,114,101,116,1,1,0,0,0,0,0,0,58,14,36,108,111,111,107,117,112,95,115,101,108,95,53,56,1,1,0,0,0,0,0,0,59,14,36,108,111,111,107,117,112,95,115,101,108,95,53,57,1,1,0,0,0,0,0,0,60,14,36,108,111,111,107,117,112,95,115,101,108,95,54,48,1,1,0,0,0,0,0,0,61,21,40,105,110,118,32,114,101,97,100,95,49,54,58,98,111,102,102,115,101,116,41,0,0,0]
theorem C48_7p0bound : C48_7p0.all wordBound = true := (by decide : [56,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,57,4,36,114,101,116,1,1,0,0,0,0,0,0,58,14,36,108,111,111,107,117,112,95,115,101,108,95,53,56,1,1,0,0,0,0,0,0,59,14,36,108,111,111,107,117,112,95,115,101,108,95,53,57,1,1,0,0,0,0,0,0,60,14,36,108,111,111,107,117,112,95,115,101,108,95,54,48,1,1,0,0,0,0,0,0,61,21,40,105,110,118,32,114,101,97,100,95,49,54,58,98,111,102,102,115,101,116,41,0,0,0].all wordBound = true)

def C48_7p1 : List Nat := [0,0,0,1,0,62,27,40,105,110,118,32,40,45,32,114,101,97,100,95,49,54,58,98,111,102,102,115,101,116,32,49,41,41,0,0,0,0,0,0,1,0,63,27,40,105,110,118,32,40,45,32,114,101,97,100,95,49,54,58,98,111,102,102,115,101,116,32,50,41,41,0,0,0,0,0,0,1,0]
theorem C48_7p1bound : C48_7p1.all wordBound = true := (by decide : [0,0,0,1,0,62,27,40,105,110,118,32,40,45,32,114,101,97,100,95,49,54,58,98,111,102,102,115,101,116,32,49,41,41,0,0,0,0,0,0,1,0,63,27,40,105,110,118,32,40,45,32,114,101,97,100,95,49,54,58,98,111,102,102,115,101,116,32,50,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C48_7words : List Nat := C48_7p0 ++ C48_7p1

theorem C48_7wire : C48_7.flatMap columnWords = C48_7words := by
  rfl

theorem C48_7wordBound : C48_7words.all wordBound = true := by
  simp only [C48_7words,List.all_append,C48_7p0bound,C48_7p1bound]
  try rfl

theorem C48_7bounded : ∀ n ∈ C48_7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C48_7wordBound

theorem C48_7length : C48_7.length = 8 := by rfl

def M48 : Module := ⟨48, [114,101,97,100,95,49,54], false, false, C48_0 ++ C48_1 ++ C48_2 ++ C48_3 ++ C48_4 ++ C48_5 ++ C48_6 ++ C48_7, ((List.range 0).map (fun n => [n]))⟩

def M48prefix : List Nat := [48,7,114,101,97,100,95,49,54,0,0,0,0,64]
theorem M48prefixwordBound : M48prefix.all wordBound = true := by decide

def M48words : List Nat := M48prefix ++ C48_0words ++ C48_1words ++ C48_2words ++ C48_3words ++ C48_4words ++ C48_5words ++ C48_6words ++ C48_7words ++ [0]

theorem M48wire : module.encode M48 = M48words := by
  rw [module_fast]
  simp only [M48,moduleWords,List.length_append,List.flatMap_append,C48_0length,C48_1length,C48_2length,C48_3length,C48_4length,C48_5length,C48_6length,C48_7length,C48_0wire,C48_1wire,C48_2wire,C48_3wire,C48_4wire,C48_5wire,C48_6wire,C48_7wire]
  rfl

theorem M48wordBound : M48words.all wordBound = true := by
  simp only [M48words,List.all_append,M48prefixwordBound,C48_0wordBound,C48_1wordBound,C48_2wordBound,C48_3wordBound,C48_4wordBound,C48_5wordBound,C48_6wordBound,C48_7wordBound]
  decide

theorem M48bounded : ∀ n ∈ M48words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M48wordBound

end DivRemFV.Replay
