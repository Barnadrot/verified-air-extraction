import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C61_0 : List Column := [⟨0, [97,39,51], (some (16)), true, false, false⟩,⟨1, [97,39,50], (some (16)), true, false, false⟩,⟨2, [97,39,49], (some (16)), true, false, false⟩,⟨3, [97,39,48], (some (16)), true, false, false⟩,⟨4, [98,39,51], (some (16)), true, false, false⟩,⟨5, [98,39,50], (some (16)), true, false, false⟩,⟨6, [98,39,49], (some (16)), true, false, false⟩,⟨7, [98,39,48], (some (16)), true, false, false⟩]

def C61_0p0 : List Nat := [0,3,97,39,51,1,16,1,0,0,0,0,0,1,3,97,39,50,1,16,1,0,0,0,0,0,2,3,97,39,49,1,16,1,0,0,0,0,0,3,3,97,39,48,1,16,1,0,0,0,0,0,4,3,98,39,51,1,16,1,0,0,0,0,0,5,3,98,39,50,1,16,1,0,0,0,0,0,6,3,98,39,49,1,16,1,0,0,0,0,0,7,3,98,39,48,1,16,1,0,0,0,0,0]
theorem C61_0p0bound : C61_0p0.all wordBound = true := (by decide : [0,3,97,39,51,1,16,1,0,0,0,0,0,1,3,97,39,50,1,16,1,0,0,0,0,0,2,3,97,39,49,1,16,1,0,0,0,0,0,3,3,97,39,48,1,16,1,0,0,0,0,0,4,3,98,39,51,1,16,1,0,0,0,0,0,5,3,98,39,50,1,16,1,0,0,0,0,0,6,3,98,39,49,1,16,1,0,0,0,0,0,7,3,98,39,48,1,16,1,0,0,0,0,0].all wordBound = true)

def C61_0words : List Nat := C61_0p0

theorem C61_0wire : C61_0.flatMap columnWords = C61_0words := by
  rfl

theorem C61_0wordBound : C61_0words.all wordBound = true := by
  simp only [C61_0words,List.all_append,C61_0p0bound]
  try rfl

theorem C61_0bounded : ∀ n ∈ C61_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_0wordBound

theorem C61_0length : C61_0.length = 8 := by rfl

def C61_1 : List Column := [⟨8, [113,39,51], (some (16)), false, true, false⟩,⟨9, [113,39,50], (some (16)), false, true, false⟩,⟨10, [113,39,49], (some (16)), false, true, false⟩,⟨11, [113,39,48], (some (16)), false, true, false⟩,⟨12, [114,39,51], (some (16)), false, true, false⟩,⟨13, [114,39,50], (some (16)), false, true, false⟩,⟨14, [114,39,49], (some (16)), false, true, false⟩,⟨15, [114,39,48], (some (16)), false, true, false⟩]

def C61_1p0 : List Nat := [8,3,113,39,51,1,16,0,0,1,0,0,0,9,3,113,39,50,1,16,0,0,1,0,0,0,10,3,113,39,49,1,16,0,0,1,0,0,0,11,3,113,39,48,1,16,0,0,1,0,0,0,12,3,114,39,51,1,16,0,0,1,0,0,0,13,3,114,39,50,1,16,0,0,1,0,0,0,14,3,114,39,49,1,16,0,0,1,0,0,0,15,3,114,39,48,1,16,0,0,1,0,0,0]
theorem C61_1p0bound : C61_1p0.all wordBound = true := (by decide : [8,3,113,39,51,1,16,0,0,1,0,0,0,9,3,113,39,50,1,16,0,0,1,0,0,0,10,3,113,39,49,1,16,0,0,1,0,0,0,11,3,113,39,48,1,16,0,0,1,0,0,0,12,3,114,39,51,1,16,0,0,1,0,0,0,13,3,114,39,50,1,16,0,0,1,0,0,0,14,3,114,39,49,1,16,0,0,1,0,0,0,15,3,114,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C61_1words : List Nat := C61_1p0

theorem C61_1wire : C61_1.flatMap columnWords = C61_1words := by
  rfl

theorem C61_1wordBound : C61_1words.all wordBound = true := by
  simp only [C61_1words,List.all_append,C61_1p0bound]
  try rfl

theorem C61_1bounded : ∀ n ∈ C61_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_1wordBound

theorem C61_1length : C61_1.length = 8 := by rfl

def C61_2 : List Column := [⟨16, [119,36,52,39,51], (some (16)), false, false, false⟩,⟨17, [119,36,52,39,50], (some (16)), false, false, false⟩,⟨18, [119,36,52,39,49], (some (16)), false, false, false⟩,⟨19, [119,36,52,39,48], (some (16)), false, false, false⟩,⟨20, [113,121,36,53,39,51], (some (16)), false, false, false⟩,⟨21, [113,121,36,53,39,50], (some (16)), false, false, false⟩,⟨22, [113,121,36,53,39,49], (some (16)), false, false, false⟩,⟨23, [113,121,36,53,39,48], (some (16)), false, false, false⟩]

def C61_2p0 : List Nat := [16,5,119,36,52,39,51,1,16,0,0,0,0,0,0,17,5,119,36,52,39,50,1,16,0,0,0,0,0,0,18,5,119,36,52,39,49,1,16,0,0,0,0,0,0,19,5,119,36,52,39,48,1,16,0,0,0,0,0,0,20,6,113,121,36,53,39,51,1,16,0,0,0,0,0,0,21,6,113,121,36,53,39,50,1,16,0,0,0,0,0,0,22,6,113,121,36,53,39,49,1,16,0,0,0,0,0,0,23,6,113,121,36,53,39,48,1,16,0,0,0,0,0,0]
theorem C61_2p0bound : C61_2p0.all wordBound = true := (by decide : [16,5,119,36,52,39,51,1,16,0,0,0,0,0,0,17,5,119,36,52,39,50,1,16,0,0,0,0,0,0,18,5,119,36,52,39,49,1,16,0,0,0,0,0,0,19,5,119,36,52,39,48,1,16,0,0,0,0,0,0,20,6,113,121,36,53,39,51,1,16,0,0,0,0,0,0,21,6,113,121,36,53,39,50,1,16,0,0,0,0,0,0,22,6,113,121,36,53,39,49,1,16,0,0,0,0,0,0,23,6,113,121,36,53,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C61_2words : List Nat := C61_2p0

theorem C61_2wire : C61_2.flatMap columnWords = C61_2words := by
  rfl

theorem C61_2wordBound : C61_2words.all wordBound = true := by
  simp only [C61_2words,List.all_append,C61_2p0bound]
  try rfl

theorem C61_2bounded : ∀ n ∈ C61_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_2wordBound

theorem C61_2length : C61_2.length = 8 := by rfl

def C61_3 : List Column := [⟨24, [113,121,95,112,108,117,115,95,114,36,54,39,51], (some (16)), false, false, false⟩,⟨25, [113,121,95,112,108,117,115,95,114,36,54,39,50], (some (16)), false, false, false⟩,⟨26, [113,121,95,112,108,117,115,95,114,36,54,39,49], (some (16)), false, false, false⟩,⟨27, [113,121,95,112,108,117,115,95,114,36,54,39,48], (some (16)), false, false, false⟩,⟨28, [114,119,49,36,55,39,51], (some (16)), false, false, false⟩,⟨29, [114,119,49,36,55,39,50], (some (16)), false, false, false⟩,⟨30, [114,119,49,36,55,39,49], (some (16)), false, false, false⟩,⟨31, [114,119,49,36,55,39,48], (some (16)), false, false, false⟩]

def C61_3p0 : List Nat := [24,13,113,121,95,112,108,117,115,95,114,36,54,39,51,1,16,0,0,0,0,0,0,25,13,113,121,95,112,108,117,115,95,114,36,54,39,50,1,16,0,0,0,0,0,0,26,13,113,121,95,112,108,117,115,95,114,36,54,39,49,1,16,0,0,0,0,0,0,27,13,113,121,95,112,108,117,115,95,114,36,54,39,48,1,16,0,0,0,0,0,0,28,7,114,119,49,36,55,39,51,1,16,0,0,0,0,0,0,29,7,114,119,49,36,55,39,50,1,16,0,0,0,0,0,0,30,7]
theorem C61_3p0bound : C61_3p0.all wordBound = true := (by decide : [24,13,113,121,95,112,108,117,115,95,114,36,54,39,51,1,16,0,0,0,0,0,0,25,13,113,121,95,112,108,117,115,95,114,36,54,39,50,1,16,0,0,0,0,0,0,26,13,113,121,95,112,108,117,115,95,114,36,54,39,49,1,16,0,0,0,0,0,0,27,13,113,121,95,112,108,117,115,95,114,36,54,39,48,1,16,0,0,0,0,0,0,28,7,114,119,49,36,55,39,51,1,16,0,0,0,0,0,0,29,7,114,119,49,36,55,39,50,1,16,0,0,0,0,0,0,30,7].all wordBound = true)

def C61_3p1 : List Nat := [114,119,49,36,55,39,49,1,16,0,0,0,0,0,0,31,7,114,119,49,36,55,39,48,1,16,0,0,0,0,0,0]
theorem C61_3p1bound : C61_3p1.all wordBound = true := (by decide : [114,119,49,36,55,39,49,1,16,0,0,0,0,0,0,31,7,114,119,49,36,55,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C61_3words : List Nat := C61_3p0 ++ C61_3p1

theorem C61_3wire : C61_3.flatMap columnWords = C61_3words := by
  rfl

theorem C61_3wordBound : C61_3words.all wordBound = true := by
  simp only [C61_3words,List.all_append,C61_3p0bound,C61_3p1bound]
  try rfl

theorem C61_3bounded : ∀ n ∈ C61_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_3wordBound

theorem C61_3length : C61_3.length = 8 := by rfl

def C61_4 : List Column := [⟨32, [36,99,115,116,95,48], (some (0)), false, false, false⟩,⟨33, [102,115,99,36,57], (some (1)), false, false, false⟩,⟨34, [115,36,51,52], (some (15)), false, false, false⟩,⟨35, [115,36,51,53], (some (1)), false, false, false⟩,⟨36, [115,36,51,54], (some (14)), false, false, false⟩,⟨37, [115,36,51,55], (some (2)), false, false, false⟩,⟨38, [115,36,51,56], (some (13)), false, false, false⟩,⟨39, [115,36,51,57], (some (3)), false, false, false⟩]

def C61_4p0 : List Nat := [32,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,33,5,102,115,99,36,57,1,1,0,0,0,0,0,0,34,4,115,36,51,52,1,15,0,0,0,0,0,0,35,4,115,36,51,53,1,1,0,0,0,0,0,0,36,4,115,36,51,54,1,14,0,0,0,0,0,0,37,4,115,36,51,55,1,2,0,0,0,0,0,0,38,4,115,36,51,56,1,13,0,0,0,0,0,0,39,4,115,36,51,57,1,3,0,0,0,0,0,0]
theorem C61_4p0bound : C61_4p0.all wordBound = true := (by decide : [32,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,33,5,102,115,99,36,57,1,1,0,0,0,0,0,0,34,4,115,36,51,52,1,15,0,0,0,0,0,0,35,4,115,36,51,53,1,1,0,0,0,0,0,0,36,4,115,36,51,54,1,14,0,0,0,0,0,0,37,4,115,36,51,55,1,2,0,0,0,0,0,0,38,4,115,36,51,56,1,13,0,0,0,0,0,0,39,4,115,36,51,57,1,3,0,0,0,0,0,0].all wordBound = true)

def C61_4words : List Nat := C61_4p0

theorem C61_4wire : C61_4.flatMap columnWords = C61_4words := by
  rfl

theorem C61_4wordBound : C61_4words.all wordBound = true := by
  simp only [C61_4words,List.all_append,C61_4p0bound]
  try rfl

theorem C61_4bounded : ∀ n ∈ C61_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_4wordBound

theorem C61_4length : C61_4.length = 8 := by rfl

def C61_5 : List Column := [⟨40, [115,36,52,48], (some (12)), false, false, false⟩,⟨41, [115,36,52,49], (some (4)), false, false, false⟩,⟨42, [115,36,52,50], (some (15)), false, false, false⟩,⟨43, [115,36,52,51], (some (15)), false, false, false⟩,⟨44, [115,36,52,52], (some (15)), false, false, false⟩,⟨45, [115,36,52,53], (some (15)), false, false, false⟩,⟨46, [115,36,52,54], (some (1)), false, false, false⟩,⟨47, [115,36,52,55], (some (14)), false, false, false⟩]

def C61_5p0 : List Nat := [40,4,115,36,52,48,1,12,0,0,0,0,0,0,41,4,115,36,52,49,1,4,0,0,0,0,0,0,42,4,115,36,52,50,1,15,0,0,0,0,0,0,43,4,115,36,52,51,1,15,0,0,0,0,0,0,44,4,115,36,52,52,1,15,0,0,0,0,0,0,45,4,115,36,52,53,1,15,0,0,0,0,0,0,46,4,115,36,52,54,1,1,0,0,0,0,0,0,47,4,115,36,52,55,1,14,0,0,0,0,0,0]
theorem C61_5p0bound : C61_5p0.all wordBound = true := (by decide : [40,4,115,36,52,48,1,12,0,0,0,0,0,0,41,4,115,36,52,49,1,4,0,0,0,0,0,0,42,4,115,36,52,50,1,15,0,0,0,0,0,0,43,4,115,36,52,51,1,15,0,0,0,0,0,0,44,4,115,36,52,52,1,15,0,0,0,0,0,0,45,4,115,36,52,53,1,15,0,0,0,0,0,0,46,4,115,36,52,54,1,1,0,0,0,0,0,0,47,4,115,36,52,55,1,14,0,0,0,0,0,0].all wordBound = true)

def C61_5words : List Nat := C61_5p0

theorem C61_5wire : C61_5.flatMap columnWords = C61_5words := by
  rfl

theorem C61_5wordBound : C61_5words.all wordBound = true := by
  simp only [C61_5words,List.all_append,C61_5p0bound]
  try rfl

theorem C61_5bounded : ∀ n ∈ C61_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_5wordBound

theorem C61_5length : C61_5.length = 8 := by rfl

def C61_6 : List Column := [⟨48, [115,36,52,56], (some (2)), false, false, false⟩,⟨49, [115,36,52,57], (some (13)), false, false, false⟩,⟨50, [115,36,53,48], (some (3)), false, false, false⟩,⟨51, [115,36,53,49], (some (12)), false, false, false⟩,⟨52, [115,36,53,50], (some (4)), false, false, false⟩,⟨53, [115,36,53,51], (some (15)), false, false, false⟩,⟨54, [115,36,53,52], (some (15)), false, false, false⟩,⟨55, [115,36,53,53], (some (15)), false, false, false⟩]

def C61_6p0 : List Nat := [48,4,115,36,52,56,1,2,0,0,0,0,0,0,49,4,115,36,52,57,1,13,0,0,0,0,0,0,50,4,115,36,53,48,1,3,0,0,0,0,0,0,51,4,115,36,53,49,1,12,0,0,0,0,0,0,52,4,115,36,53,50,1,4,0,0,0,0,0,0,53,4,115,36,53,51,1,15,0,0,0,0,0,0,54,4,115,36,53,52,1,15,0,0,0,0,0,0,55,4,115,36,53,53,1,15,0,0,0,0,0,0]
theorem C61_6p0bound : C61_6p0.all wordBound = true := (by decide : [48,4,115,36,52,56,1,2,0,0,0,0,0,0,49,4,115,36,52,57,1,13,0,0,0,0,0,0,50,4,115,36,53,48,1,3,0,0,0,0,0,0,51,4,115,36,53,49,1,12,0,0,0,0,0,0,52,4,115,36,53,50,1,4,0,0,0,0,0,0,53,4,115,36,53,51,1,15,0,0,0,0,0,0,54,4,115,36,53,52,1,15,0,0,0,0,0,0,55,4,115,36,53,53,1,15,0,0,0,0,0,0].all wordBound = true)

def C61_6words : List Nat := C61_6p0

theorem C61_6wire : C61_6.flatMap columnWords = C61_6words := by
  rfl

theorem C61_6wordBound : C61_6words.all wordBound = true := by
  simp only [C61_6words,List.all_append,C61_6p0bound]
  try rfl

theorem C61_6bounded : ∀ n ∈ C61_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_6wordBound

theorem C61_6length : C61_6.length = 8 := by rfl

def C61_7 : List Column := [⟨56, [112,112,36,53,54], (some (15)), false, false, false⟩,⟨57, [112,112,36,53,55], (some (15)), false, false, false⟩,⟨58, [112,112,36,53,56], (some (15)), false, false, false⟩,⟨59, [112,112,36,53,57], (some (15)), false, false, false⟩,⟨60, [112,112,36,54,48], (some (15)), false, false, false⟩,⟨61, [112,112,36,54,49], (some (15)), false, false, false⟩,⟨62, [112,112,36,54,50], (some (15)), false, false, false⟩,⟨63, [112,112,36,54,51], (some (15)), false, false, false⟩]

def C61_7p0 : List Nat := [56,5,112,112,36,53,54,1,15,0,0,0,0,0,0,57,5,112,112,36,53,55,1,15,0,0,0,0,0,0,58,5,112,112,36,53,56,1,15,0,0,0,0,0,0,59,5,112,112,36,53,57,1,15,0,0,0,0,0,0,60,5,112,112,36,54,48,1,15,0,0,0,0,0,0,61,5,112,112,36,54,49,1,15,0,0,0,0,0,0,62,5,112,112,36,54,50,1,15,0,0,0,0,0,0,63,5,112,112,36,54,51,1,15,0,0,0,0,0,0]
theorem C61_7p0bound : C61_7p0.all wordBound = true := (by decide : [56,5,112,112,36,53,54,1,15,0,0,0,0,0,0,57,5,112,112,36,53,55,1,15,0,0,0,0,0,0,58,5,112,112,36,53,56,1,15,0,0,0,0,0,0,59,5,112,112,36,53,57,1,15,0,0,0,0,0,0,60,5,112,112,36,54,48,1,15,0,0,0,0,0,0,61,5,112,112,36,54,49,1,15,0,0,0,0,0,0,62,5,112,112,36,54,50,1,15,0,0,0,0,0,0,63,5,112,112,36,54,51,1,15,0,0,0,0,0,0].all wordBound = true)

def C61_7words : List Nat := C61_7p0

theorem C61_7wire : C61_7.flatMap columnWords = C61_7words := by
  rfl

theorem C61_7wordBound : C61_7words.all wordBound = true := by
  simp only [C61_7words,List.all_append,C61_7p0bound]
  try rfl

theorem C61_7bounded : ∀ n ∈ C61_7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_7wordBound

theorem C61_7length : C61_7.length = 8 := by rfl

def C61_8 : List Column := [⟨64, [112,112,36,54,52], (some (15)), false, false, false⟩,⟨65, [112,112,36,54,53], (some (4)), false, false, false⟩,⟨66, [112,112,36,54,54], (some (15)), false, false, false⟩,⟨67, [112,112,36,54,55], (some (15)), false, false, false⟩,⟨68, [112,112,36,54,56], (some (15)), false, false, false⟩,⟨69, [112,112,36,54,57], (some (15)), false, false, false⟩,⟨70, [112,112,36,55,48], (some (15)), false, false, false⟩,⟨71, [112,112,36,55,49], (some (15)), false, false, false⟩]

def C61_8p0 : List Nat := [64,5,112,112,36,54,52,1,15,0,0,0,0,0,0,65,5,112,112,36,54,53,1,4,0,0,0,0,0,0,66,5,112,112,36,54,54,1,15,0,0,0,0,0,0,67,5,112,112,36,54,55,1,15,0,0,0,0,0,0,68,5,112,112,36,54,56,1,15,0,0,0,0,0,0,69,5,112,112,36,54,57,1,15,0,0,0,0,0,0,70,5,112,112,36,55,48,1,15,0,0,0,0,0,0,71,5,112,112,36,55,49,1,15,0,0,0,0,0,0]
theorem C61_8p0bound : C61_8p0.all wordBound = true := (by decide : [64,5,112,112,36,54,52,1,15,0,0,0,0,0,0,65,5,112,112,36,54,53,1,4,0,0,0,0,0,0,66,5,112,112,36,54,54,1,15,0,0,0,0,0,0,67,5,112,112,36,54,55,1,15,0,0,0,0,0,0,68,5,112,112,36,54,56,1,15,0,0,0,0,0,0,69,5,112,112,36,54,57,1,15,0,0,0,0,0,0,70,5,112,112,36,55,48,1,15,0,0,0,0,0,0,71,5,112,112,36,55,49,1,15,0,0,0,0,0,0].all wordBound = true)

def C61_8words : List Nat := C61_8p0

theorem C61_8wire : C61_8.flatMap columnWords = C61_8words := by
  rfl

theorem C61_8wordBound : C61_8words.all wordBound = true := by
  simp only [C61_8words,List.all_append,C61_8p0bound]
  try rfl

theorem C61_8bounded : ∀ n ∈ C61_8words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_8wordBound

theorem C61_8length : C61_8.length = 8 := by rfl

def C61_9 : List Column := [⟨72, [112,112,36,55,50], (some (15)), false, false, false⟩,⟨73, [112,112,36,55,51], (some (15)), false, false, false⟩,⟨74, [112,112,36,55,52], (some (15)), false, false, false⟩,⟨75, [112,112,36,55,53], (some (4)), false, false, false⟩,⟨76, [112,112,36,55,54], (some (15)), false, false, false⟩,⟨77, [112,112,36,55,55], (some (15)), false, false, false⟩,⟨78, [112,112,36,55,56], (some (15)), false, false, false⟩,⟨79, [112,112,36,55,57], (some (15)), false, false, false⟩]

def C61_9p0 : List Nat := [72,5,112,112,36,55,50,1,15,0,0,0,0,0,0,73,5,112,112,36,55,51,1,15,0,0,0,0,0,0,74,5,112,112,36,55,52,1,15,0,0,0,0,0,0,75,5,112,112,36,55,53,1,4,0,0,0,0,0,0,76,5,112,112,36,55,54,1,15,0,0,0,0,0,0,77,5,112,112,36,55,55,1,15,0,0,0,0,0,0,78,5,112,112,36,55,56,1,15,0,0,0,0,0,0,79,5,112,112,36,55,57,1,15,0,0,0,0,0,0]
theorem C61_9p0bound : C61_9p0.all wordBound = true := (by decide : [72,5,112,112,36,55,50,1,15,0,0,0,0,0,0,73,5,112,112,36,55,51,1,15,0,0,0,0,0,0,74,5,112,112,36,55,52,1,15,0,0,0,0,0,0,75,5,112,112,36,55,53,1,4,0,0,0,0,0,0,76,5,112,112,36,55,54,1,15,0,0,0,0,0,0,77,5,112,112,36,55,55,1,15,0,0,0,0,0,0,78,5,112,112,36,55,56,1,15,0,0,0,0,0,0,79,5,112,112,36,55,57,1,15,0,0,0,0,0,0].all wordBound = true)

def C61_9words : List Nat := C61_9p0

theorem C61_9wire : C61_9.flatMap columnWords = C61_9words := by
  rfl

theorem C61_9wordBound : C61_9words.all wordBound = true := by
  simp only [C61_9words,List.all_append,C61_9p0bound]
  try rfl

theorem C61_9bounded : ∀ n ∈ C61_9words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_9wordBound

theorem C61_9length : C61_9.length = 8 := by rfl

def C61_10 : List Column := [⟨80, [112,112,36,56,48], (some (15)), false, false, false⟩,⟨81, [112,112,36,56,49], (some (15)), false, false, false⟩,⟨82, [112,112,36,56,50], (some (15)), false, false, false⟩,⟨83, [112,112,36,56,51], (some (15)), false, false, false⟩,⟨84, [112,112,36,56,52], (some (15)), false, false, false⟩,⟨85, [112,112,36,56,53], (some (4)), false, false, false⟩,⟨86, [112,112,36,56,54], (some (15)), false, false, false⟩,⟨87, [112,112,36,56,55], (some (15)), false, false, false⟩]

def C61_10p0 : List Nat := [80,5,112,112,36,56,48,1,15,0,0,0,0,0,0,81,5,112,112,36,56,49,1,15,0,0,0,0,0,0,82,5,112,112,36,56,50,1,15,0,0,0,0,0,0,83,5,112,112,36,56,51,1,15,0,0,0,0,0,0,84,5,112,112,36,56,52,1,15,0,0,0,0,0,0,85,5,112,112,36,56,53,1,4,0,0,0,0,0,0,86,5,112,112,36,56,54,1,15,0,0,0,0,0,0,87,5,112,112,36,56,55,1,15,0,0,0,0,0,0]
theorem C61_10p0bound : C61_10p0.all wordBound = true := (by decide : [80,5,112,112,36,56,48,1,15,0,0,0,0,0,0,81,5,112,112,36,56,49,1,15,0,0,0,0,0,0,82,5,112,112,36,56,50,1,15,0,0,0,0,0,0,83,5,112,112,36,56,51,1,15,0,0,0,0,0,0,84,5,112,112,36,56,52,1,15,0,0,0,0,0,0,85,5,112,112,36,56,53,1,4,0,0,0,0,0,0,86,5,112,112,36,56,54,1,15,0,0,0,0,0,0,87,5,112,112,36,56,55,1,15,0,0,0,0,0,0].all wordBound = true)

def C61_10words : List Nat := C61_10p0

theorem C61_10wire : C61_10.flatMap columnWords = C61_10words := by
  rfl

theorem C61_10wordBound : C61_10words.all wordBound = true := by
  simp only [C61_10words,List.all_append,C61_10p0bound]
  try rfl

theorem C61_10bounded : ∀ n ∈ C61_10words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_10wordBound

theorem C61_10length : C61_10.length = 8 := by rfl

def C61_11 : List Column := [⟨88, [112,112,36,56,56], (some (15)), false, false, false⟩,⟨89, [112,112,36,56,57], (some (15)), false, false, false⟩,⟨90, [112,112,36,57,48], (some (15)), false, false, false⟩,⟨91, [112,112,36,57,49], (some (15)), false, false, false⟩,⟨92, [112,112,36,57,50], (some (15)), false, false, false⟩,⟨93, [112,112,36,57,51], (some (15)), false, false, false⟩,⟨94, [112,112,36,57,52], (some (15)), false, false, false⟩,⟨95, [112,112,36,57,53], (some (4)), false, false, false⟩]

def C61_11p0 : List Nat := [88,5,112,112,36,56,56,1,15,0,0,0,0,0,0,89,5,112,112,36,56,57,1,15,0,0,0,0,0,0,90,5,112,112,36,57,48,1,15,0,0,0,0,0,0,91,5,112,112,36,57,49,1,15,0,0,0,0,0,0,92,5,112,112,36,57,50,1,15,0,0,0,0,0,0,93,5,112,112,36,57,51,1,15,0,0,0,0,0,0,94,5,112,112,36,57,52,1,15,0,0,0,0,0,0,95,5,112,112,36,57,53,1,4,0,0,0,0,0,0]
theorem C61_11p0bound : C61_11p0.all wordBound = true := (by decide : [88,5,112,112,36,56,56,1,15,0,0,0,0,0,0,89,5,112,112,36,56,57,1,15,0,0,0,0,0,0,90,5,112,112,36,57,48,1,15,0,0,0,0,0,0,91,5,112,112,36,57,49,1,15,0,0,0,0,0,0,92,5,112,112,36,57,50,1,15,0,0,0,0,0,0,93,5,112,112,36,57,51,1,15,0,0,0,0,0,0,94,5,112,112,36,57,52,1,15,0,0,0,0,0,0,95,5,112,112,36,57,53,1,4,0,0,0,0,0,0].all wordBound = true)

def C61_11words : List Nat := C61_11p0

theorem C61_11wire : C61_11.flatMap columnWords = C61_11words := by
  rfl

theorem C61_11wordBound : C61_11words.all wordBound = true := by
  simp only [C61_11words,List.all_append,C61_11p0bound]
  try rfl

theorem C61_11bounded : ∀ n ∈ C61_11words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_11wordBound

theorem C61_11length : C61_11.length = 8 := by rfl

def C61_12 : List Column := [⟨96, [112,112,36,57,54], (some (15)), false, false, false⟩,⟨97, [112,112,36,57,55], (some (4)), false, false, false⟩,⟨98, [112,112,36,57,56], (some (15)), false, false, false⟩,⟨99, [112,112,36,57,57], (some (4)), false, false, false⟩,⟨100, [112,112,36,49,48,48], (some (15)), false, false, false⟩,⟨101, [112,112,36,49,48,49], (some (4)), false, false, false⟩,⟨102, [112,112,36,49,48,50], (some (15)), false, false, false⟩,⟨103, [112,112,36,49,48,51], (some (4)), false, false, false⟩]

def C61_12p0 : List Nat := [96,5,112,112,36,57,54,1,15,0,0,0,0,0,0,97,5,112,112,36,57,55,1,4,0,0,0,0,0,0,98,5,112,112,36,57,56,1,15,0,0,0,0,0,0,99,5,112,112,36,57,57,1,4,0,0,0,0,0,0,100,6,112,112,36,49,48,48,1,15,0,0,0,0,0,0,101,6,112,112,36,49,48,49,1,4,0,0,0,0,0,0,102,6,112,112,36,49,48,50,1,15,0,0,0,0,0,0,103,6,112,112,36,49,48,51,1,4,0,0,0,0,0,0]
theorem C61_12p0bound : C61_12p0.all wordBound = true := (by decide : [96,5,112,112,36,57,54,1,15,0,0,0,0,0,0,97,5,112,112,36,57,55,1,4,0,0,0,0,0,0,98,5,112,112,36,57,56,1,15,0,0,0,0,0,0,99,5,112,112,36,57,57,1,4,0,0,0,0,0,0,100,6,112,112,36,49,48,48,1,15,0,0,0,0,0,0,101,6,112,112,36,49,48,49,1,4,0,0,0,0,0,0,102,6,112,112,36,49,48,50,1,15,0,0,0,0,0,0,103,6,112,112,36,49,48,51,1,4,0,0,0,0,0,0].all wordBound = true)

def C61_12words : List Nat := C61_12p0

theorem C61_12wire : C61_12.flatMap columnWords = C61_12words := by
  rfl

theorem C61_12wordBound : C61_12words.all wordBound = true := by
  simp only [C61_12words,List.all_append,C61_12p0bound]
  try rfl

theorem C61_12bounded : ∀ n ∈ C61_12words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_12wordBound

theorem C61_12length : C61_12.length = 8 := by rfl

def C61_13 : List Column := [⟨104, [112,112,36,49,48,52], (some (8)), false, false, false⟩,⟨105, [109,36,49,48,53], (some (1)), false, false, false⟩,⟨106, [109,36,49,48,54], (some (14)), false, false, false⟩,⟨107, [99,36,49,48,55], (some (2)), false, false, false⟩,⟨108, [109,36,49,48,56], (some (2)), false, false, false⟩,⟨109, [109,36,49,48,57], (some (13)), false, false, false⟩,⟨110, [99,36,49,49,48], (some (3)), false, false, false⟩,⟨111, [109,36,49,49,49], (some (3)), false, false, false⟩]

def C61_13p0 : List Nat := [104,6,112,112,36,49,48,52,1,8,0,0,0,0,0,0,105,5,109,36,49,48,53,1,1,0,0,0,0,0,0,106,5,109,36,49,48,54,1,14,0,0,0,0,0,0,107,5,99,36,49,48,55,1,2,0,0,0,0,0,0,108,5,109,36,49,48,56,1,2,0,0,0,0,0,0,109,5,109,36,49,48,57,1,13,0,0,0,0,0,0,110,5,99,36,49,49,48,1,3,0,0,0,0,0,0,111,5,109,36,49,49,49,1,3,0,0,0,0,0,0]
theorem C61_13p0bound : C61_13p0.all wordBound = true := (by decide : [104,6,112,112,36,49,48,52,1,8,0,0,0,0,0,0,105,5,109,36,49,48,53,1,1,0,0,0,0,0,0,106,5,109,36,49,48,54,1,14,0,0,0,0,0,0,107,5,99,36,49,48,55,1,2,0,0,0,0,0,0,108,5,109,36,49,48,56,1,2,0,0,0,0,0,0,109,5,109,36,49,48,57,1,13,0,0,0,0,0,0,110,5,99,36,49,49,48,1,3,0,0,0,0,0,0,111,5,109,36,49,49,49,1,3,0,0,0,0,0,0].all wordBound = true)

def C61_13words : List Nat := C61_13p0

theorem C61_13wire : C61_13.flatMap columnWords = C61_13words := by
  rfl

theorem C61_13wordBound : C61_13words.all wordBound = true := by
  simp only [C61_13words,List.all_append,C61_13p0bound]
  try rfl

theorem C61_13bounded : ∀ n ∈ C61_13words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_13wordBound

theorem C61_13length : C61_13.length = 8 := by rfl

def C61_14 : List Column := [⟨112, [109,36,49,49,50], (some (12)), false, false, false⟩,⟨113, [99,36,49,49,51], (some (3)), false, false, false⟩,⟨114, [109,36,49,49,52], (some (4)), false, false, false⟩,⟨115, [99,36,49,49,53], (some (1)), false, false, false⟩,⟨116, [99,36,49,49,54], (some (1)), false, false, false⟩,⟨117, [99,36,49,49,55], (some (1)), false, false, false⟩,⟨118, [99,36,49,49,56], (some (1)), false, false, false⟩,⟨119, [99,36,49,49,57], (some (1)), false, false, false⟩]

def C61_14p0 : List Nat := [112,5,109,36,49,49,50,1,12,0,0,0,0,0,0,113,5,99,36,49,49,51,1,3,0,0,0,0,0,0,114,5,109,36,49,49,52,1,4,0,0,0,0,0,0,115,5,99,36,49,49,53,1,1,0,0,0,0,0,0,116,5,99,36,49,49,54,1,1,0,0,0,0,0,0,117,5,99,36,49,49,55,1,1,0,0,0,0,0,0,118,5,99,36,49,49,56,1,1,0,0,0,0,0,0,119,5,99,36,49,49,57,1,1,0,0,0,0,0,0]
theorem C61_14p0bound : C61_14p0.all wordBound = true := (by decide : [112,5,109,36,49,49,50,1,12,0,0,0,0,0,0,113,5,99,36,49,49,51,1,3,0,0,0,0,0,0,114,5,109,36,49,49,52,1,4,0,0,0,0,0,0,115,5,99,36,49,49,53,1,1,0,0,0,0,0,0,116,5,99,36,49,49,54,1,1,0,0,0,0,0,0,117,5,99,36,49,49,55,1,1,0,0,0,0,0,0,118,5,99,36,49,49,56,1,1,0,0,0,0,0,0,119,5,99,36,49,49,57,1,1,0,0,0,0,0,0].all wordBound = true)

def C61_14words : List Nat := C61_14p0

theorem C61_14wire : C61_14.flatMap columnWords = C61_14words := by
  rfl

theorem C61_14wordBound : C61_14words.all wordBound = true := by
  simp only [C61_14words,List.all_append,C61_14p0bound]
  try rfl

theorem C61_14bounded : ∀ n ∈ C61_14words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_14wordBound

theorem C61_14length : C61_14.length = 8 := by rfl

def C61_15 : List Column := [⟨120, [99,36,49,50,48], (some (1)), false, false, false⟩,⟨121, [36,114,101,116], (some (1)), false, false, false⟩,⟨122, [40,105,110,118,32,40,43,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,51,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,50,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,49,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,48,41,41], none, false, false, true⟩]

def C61_15p0 : List Nat := [120,5,99,36,49,50,48,1,1,0,0,0,0,0,0,121,4,36,114,101,116,1,1,0,0,0,0,0,0,122,77,40,105,110,118,32,40,43,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,51,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,50,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,49,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,48,41,41,0,0,0,0,0,0,1,0]
theorem C61_15p0bound : C61_15p0.all wordBound = true := (by decide : [120,5,99,36,49,50,48,1,1,0,0,0,0,0,0,121,4,36,114,101,116,1,1,0,0,0,0,0,0,122,77,40,105,110,118,32,40,43,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,51,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,50,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,49,32,100,105,118,77,111,100,95,54,52,95,117,117,58,98,39,48,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C61_15words : List Nat := C61_15p0

theorem C61_15wire : C61_15.flatMap columnWords = C61_15words := by
  rfl

theorem C61_15wordBound : C61_15words.all wordBound = true := by
  simp only [C61_15words,List.all_append,C61_15p0bound]
  try rfl

theorem C61_15bounded : ∀ n ∈ C61_15words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C61_15wordBound

theorem C61_15length : C61_15.length = 3 := by rfl

def M61 : Module := ⟨61, [100,105,118,77,111,100,95,54,52,95,117,117], false, false, C61_0 ++ C61_1 ++ C61_2 ++ C61_3 ++ C61_4 ++ C61_5 ++ C61_6 ++ C61_7 ++ C61_8 ++ C61_9 ++ C61_10 ++ C61_11 ++ C61_12 ++ C61_13 ++ C61_14 ++ C61_15, ((List.range 0).map (fun n => [n]))⟩

def M61prefix : List Nat := [61,12,100,105,118,77,111,100,95,54,52,95,117,117,0,0,0,0,123]
theorem M61prefixwordBound : M61prefix.all wordBound = true := by decide

def M61words : List Nat := M61prefix ++ C61_0words ++ C61_1words ++ C61_2words ++ C61_3words ++ C61_4words ++ C61_5words ++ C61_6words ++ C61_7words ++ C61_8words ++ C61_9words ++ C61_10words ++ C61_11words ++ C61_12words ++ C61_13words ++ C61_14words ++ C61_15words ++ [0]

theorem M61wire : module.encode M61 = M61words := by
  rw [module_fast]
  simp only [M61,moduleWords,List.length_append,List.flatMap_append,C61_0length,C61_1length,C61_2length,C61_3length,C61_4length,C61_5length,C61_6length,C61_7length,C61_8length,C61_9length,C61_10length,C61_11length,C61_12length,C61_13length,C61_14length,C61_15length,C61_0wire,C61_1wire,C61_2wire,C61_3wire,C61_4wire,C61_5wire,C61_6wire,C61_7wire,C61_8wire,C61_9wire,C61_10wire,C61_11wire,C61_12wire,C61_13wire,C61_14wire,C61_15wire]
  rfl

theorem M61wordBound : M61words.all wordBound = true := by
  simp only [M61words,List.all_append,M61prefixwordBound,C61_0wordBound,C61_1wordBound,C61_2wordBound,C61_3wordBound,C61_4wordBound,C61_5wordBound,C61_6wordBound,C61_7wordBound,C61_8wordBound,C61_9wordBound,C61_10wordBound,C61_11wordBound,C61_12wordBound,C61_13wordBound,C61_14wordBound,C61_15wordBound]
  decide

theorem M61bounded : ∀ n ∈ M61words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M61wordBound

end DivRemFV.Replay
