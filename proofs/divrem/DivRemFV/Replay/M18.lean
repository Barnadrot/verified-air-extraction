import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C18_0 : List Column := [⟨0, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨3, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨4, [106], (some (3)), false, false, false⟩,⟨5, [36,49], (some (7)), false, false, false⟩,⟨6, [36,50,39,51], (some (16)), false, false, false⟩,⟨7, [36,50,39,50], (some (16)), false, false, false⟩]

def C18_0p0 : List Nat := [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0]
theorem C18_0p0bound : C18_0p0.all wordBound = true := (by decide : [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C18_0p1 : List Nat := [4,1,106,1,3,0,0,0,0,0,0,5,2,36,49,1,7,0,0,0,0,0,0,6,4,36,50,39,51,1,16,0,0,0,0,0,0,7,4,36,50,39,50,1,16,0,0,0,0,0,0]
theorem C18_0p1bound : C18_0p1.all wordBound = true := (by decide : [4,1,106,1,3,0,0,0,0,0,0,5,2,36,49,1,7,0,0,0,0,0,0,6,4,36,50,39,51,1,16,0,0,0,0,0,0,7,4,36,50,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C18_0words : List Nat := C18_0p0 ++ C18_0p1

theorem C18_0wire : C18_0.flatMap columnWords = C18_0words := by
  rfl

theorem C18_0wordBound : C18_0words.all wordBound = true := by
  simp only [C18_0words,List.all_append,C18_0p0bound,C18_0p1bound]
  try rfl

theorem C18_0bounded : ∀ n ∈ C18_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_0wordBound

theorem C18_0length : C18_0.length = 8 := by rfl

def C18_1 : List Column := [⟨8, [36,50,39,49], (some (16)), false, false, false⟩,⟨9, [36,50,39,48], (some (16)), false, false, false⟩,⟨10, [36,51,39,51], (some (16)), false, false, false⟩,⟨11, [36,51,39,50], (some (16)), false, false, false⟩,⟨12, [36,51,39,49], (some (16)), false, false, false⟩,⟨13, [36,51,39,48], (some (16)), false, false, false⟩,⟨14, [36,52], (some (7)), false, false, false⟩,⟨15, [36,53], (some (6)), false, false, false⟩]

def C18_1p0 : List Nat := [8,4,36,50,39,49,1,16,0,0,0,0,0,0,9,4,36,50,39,48,1,16,0,0,0,0,0,0,10,4,36,51,39,51,1,16,0,0,0,0,0,0,11,4,36,51,39,50,1,16,0,0,0,0,0,0,12,4,36,51,39,49,1,16,0,0,0,0,0,0,13,4,36,51,39,48,1,16,0,0,0,0,0,0,14,2,36,52,1,7,0,0,0,0,0,0,15,2,36,53,1,6,0,0,0,0,0,0]
theorem C18_1p0bound : C18_1p0.all wordBound = true := (by decide : [8,4,36,50,39,49,1,16,0,0,0,0,0,0,9,4,36,50,39,48,1,16,0,0,0,0,0,0,10,4,36,51,39,51,1,16,0,0,0,0,0,0,11,4,36,51,39,50,1,16,0,0,0,0,0,0,12,4,36,51,39,49,1,16,0,0,0,0,0,0,13,4,36,51,39,48,1,16,0,0,0,0,0,0,14,2,36,52,1,7,0,0,0,0,0,0,15,2,36,53,1,6,0,0,0,0,0,0].all wordBound = true)

def C18_1words : List Nat := C18_1p0

theorem C18_1wire : C18_1.flatMap columnWords = C18_1words := by
  rfl

theorem C18_1wordBound : C18_1words.all wordBound = true := by
  simp only [C18_1words,List.all_append,C18_1p0bound]
  try rfl

theorem C18_1bounded : ∀ n ∈ C18_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_1wordBound

theorem C18_1length : C18_1.length = 8 := by rfl

def C18_2 : List Column := [⟨16, [36,54], (some (3)), false, false, false⟩,⟨17, [36,55], (some (7)), false, false, false⟩,⟨18, [36,56,39,51], (some (16)), false, false, false⟩,⟨19, [36,56,39,50], (some (16)), false, false, false⟩,⟨20, [36,56,39,49], (some (16)), false, false, false⟩,⟨21, [36,56,39,48], (some (16)), false, false, false⟩,⟨22, [36,57,39,51], (some (16)), false, false, false⟩,⟨23, [36,57,39,50], (some (16)), false, false, false⟩]

def C18_2p0 : List Nat := [16,2,36,54,1,3,0,0,0,0,0,0,17,2,36,55,1,7,0,0,0,0,0,0,18,4,36,56,39,51,1,16,0,0,0,0,0,0,19,4,36,56,39,50,1,16,0,0,0,0,0,0,20,4,36,56,39,49,1,16,0,0,0,0,0,0,21,4,36,56,39,48,1,16,0,0,0,0,0,0,22,4,36,57,39,51,1,16,0,0,0,0,0,0,23,4,36,57,39,50,1,16,0,0,0,0,0,0]
theorem C18_2p0bound : C18_2p0.all wordBound = true := (by decide : [16,2,36,54,1,3,0,0,0,0,0,0,17,2,36,55,1,7,0,0,0,0,0,0,18,4,36,56,39,51,1,16,0,0,0,0,0,0,19,4,36,56,39,50,1,16,0,0,0,0,0,0,20,4,36,56,39,49,1,16,0,0,0,0,0,0,21,4,36,56,39,48,1,16,0,0,0,0,0,0,22,4,36,57,39,51,1,16,0,0,0,0,0,0,23,4,36,57,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C18_2words : List Nat := C18_2p0

theorem C18_2wire : C18_2.flatMap columnWords = C18_2words := by
  rfl

theorem C18_2wordBound : C18_2words.all wordBound = true := by
  simp only [C18_2words,List.all_append,C18_2p0bound]
  try rfl

theorem C18_2bounded : ∀ n ∈ C18_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_2wordBound

theorem C18_2length : C18_2.length = 8 := by rfl

def C18_3 : List Column := [⟨24, [36,57,39,49], (some (16)), false, false, false⟩,⟨25, [36,57,39,48], (some (16)), false, false, false⟩,⟨26, [36,49,48], (some (7)), false, false, false⟩,⟨27, [36,49,49], (some (6)), false, false, false⟩,⟨28, [36,49,50], (some (3)), false, false, false⟩,⟨29, [36,49,51], (some (7)), false, false, false⟩,⟨30, [36,49,52,39,51], (some (16)), false, false, false⟩,⟨31, [36,49,52,39,50], (some (16)), false, false, false⟩]

def C18_3p0 : List Nat := [24,4,36,57,39,49,1,16,0,0,0,0,0,0,25,4,36,57,39,48,1,16,0,0,0,0,0,0,26,3,36,49,48,1,7,0,0,0,0,0,0,27,3,36,49,49,1,6,0,0,0,0,0,0,28,3,36,49,50,1,3,0,0,0,0,0,0,29,3,36,49,51,1,7,0,0,0,0,0,0,30,5,36,49,52,39,51,1,16,0,0,0,0,0,0,31,5,36,49,52,39,50,1,16,0,0,0,0,0,0]
theorem C18_3p0bound : C18_3p0.all wordBound = true := (by decide : [24,4,36,57,39,49,1,16,0,0,0,0,0,0,25,4,36,57,39,48,1,16,0,0,0,0,0,0,26,3,36,49,48,1,7,0,0,0,0,0,0,27,3,36,49,49,1,6,0,0,0,0,0,0,28,3,36,49,50,1,3,0,0,0,0,0,0,29,3,36,49,51,1,7,0,0,0,0,0,0,30,5,36,49,52,39,51,1,16,0,0,0,0,0,0,31,5,36,49,52,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C18_3words : List Nat := C18_3p0

theorem C18_3wire : C18_3.flatMap columnWords = C18_3words := by
  rfl

theorem C18_3wordBound : C18_3words.all wordBound = true := by
  simp only [C18_3words,List.all_append,C18_3p0bound]
  try rfl

theorem C18_3bounded : ∀ n ∈ C18_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_3wordBound

theorem C18_3length : C18_3.length = 8 := by rfl

def C18_4 : List Column := [⟨32, [36,49,52,39,49], (some (16)), false, false, false⟩,⟨33, [36,49,52,39,48], (some (16)), false, false, false⟩,⟨34, [36,49,53,39,51], (some (16)), false, false, false⟩,⟨35, [36,49,53,39,50], (some (16)), false, false, false⟩,⟨36, [36,49,53,39,49], (some (16)), false, false, false⟩,⟨37, [36,49,53,39,48], (some (16)), false, false, false⟩,⟨38, [36,49,54], (some (7)), false, false, false⟩,⟨39, [36,49,55], (some (6)), false, false, false⟩]

def C18_4p0 : List Nat := [32,5,36,49,52,39,49,1,16,0,0,0,0,0,0,33,5,36,49,52,39,48,1,16,0,0,0,0,0,0,34,5,36,49,53,39,51,1,16,0,0,0,0,0,0,35,5,36,49,53,39,50,1,16,0,0,0,0,0,0,36,5,36,49,53,39,49,1,16,0,0,0,0,0,0,37,5,36,49,53,39,48,1,16,0,0,0,0,0,0,38,3,36,49,54,1,7,0,0,0,0,0,0,39,3,36,49,55,1,6,0,0,0,0,0,0]
theorem C18_4p0bound : C18_4p0.all wordBound = true := (by decide : [32,5,36,49,52,39,49,1,16,0,0,0,0,0,0,33,5,36,49,52,39,48,1,16,0,0,0,0,0,0,34,5,36,49,53,39,51,1,16,0,0,0,0,0,0,35,5,36,49,53,39,50,1,16,0,0,0,0,0,0,36,5,36,49,53,39,49,1,16,0,0,0,0,0,0,37,5,36,49,53,39,48,1,16,0,0,0,0,0,0,38,3,36,49,54,1,7,0,0,0,0,0,0,39,3,36,49,55,1,6,0,0,0,0,0,0].all wordBound = true)

def C18_4words : List Nat := C18_4p0

theorem C18_4wire : C18_4.flatMap columnWords = C18_4words := by
  rfl

theorem C18_4wordBound : C18_4words.all wordBound = true := by
  simp only [C18_4words,List.all_append,C18_4p0bound]
  try rfl

theorem C18_4bounded : ∀ n ∈ C18_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_4wordBound

theorem C18_4length : C18_4.length = 8 := by rfl

def C18_5 : List Column := [⟨40, [36,49,56], (some (3)), false, false, false⟩,⟨41, [36,49,57], (some (7)), false, false, false⟩,⟨42, [36,50,48,39,51], (some (16)), false, false, false⟩,⟨43, [36,50,48,39,50], (some (16)), false, false, false⟩,⟨44, [36,50,48,39,49], (some (16)), false, false, false⟩,⟨45, [36,50,48,39,48], (some (16)), false, false, false⟩,⟨46, [36,50,49,39,51], (some (16)), false, false, false⟩,⟨47, [36,50,49,39,50], (some (16)), false, false, false⟩]

def C18_5p0 : List Nat := [40,3,36,49,56,1,3,0,0,0,0,0,0,41,3,36,49,57,1,7,0,0,0,0,0,0,42,5,36,50,48,39,51,1,16,0,0,0,0,0,0,43,5,36,50,48,39,50,1,16,0,0,0,0,0,0,44,5,36,50,48,39,49,1,16,0,0,0,0,0,0,45,5,36,50,48,39,48,1,16,0,0,0,0,0,0,46,5,36,50,49,39,51,1,16,0,0,0,0,0,0,47,5,36,50,49,39,50,1,16,0,0,0,0,0,0]
theorem C18_5p0bound : C18_5p0.all wordBound = true := (by decide : [40,3,36,49,56,1,3,0,0,0,0,0,0,41,3,36,49,57,1,7,0,0,0,0,0,0,42,5,36,50,48,39,51,1,16,0,0,0,0,0,0,43,5,36,50,48,39,50,1,16,0,0,0,0,0,0,44,5,36,50,48,39,49,1,16,0,0,0,0,0,0,45,5,36,50,48,39,48,1,16,0,0,0,0,0,0,46,5,36,50,49,39,51,1,16,0,0,0,0,0,0,47,5,36,50,49,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C18_5words : List Nat := C18_5p0

theorem C18_5wire : C18_5.flatMap columnWords = C18_5words := by
  rfl

theorem C18_5wordBound : C18_5words.all wordBound = true := by
  simp only [C18_5words,List.all_append,C18_5p0bound]
  try rfl

theorem C18_5bounded : ∀ n ∈ C18_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_5wordBound

theorem C18_5length : C18_5.length = 8 := by rfl

def C18_6 : List Column := [⟨48, [36,50,49,39,49], (some (16)), false, false, false⟩,⟨49, [36,50,49,39,48], (some (16)), false, false, false⟩,⟨50, [36,50,50], (some (7)), false, false, false⟩,⟨51, [36,50,51], (some (6)), false, false, false⟩,⟨52, [36,50,52], (some (3)), false, false, false⟩,⟨53, [36,50,53], (some (7)), false, false, false⟩,⟨54, [36,50,54,39,51], (some (16)), false, false, false⟩,⟨55, [36,50,54,39,50], (some (16)), false, false, false⟩]

def C18_6p0 : List Nat := [48,5,36,50,49,39,49,1,16,0,0,0,0,0,0,49,5,36,50,49,39,48,1,16,0,0,0,0,0,0,50,3,36,50,50,1,7,0,0,0,0,0,0,51,3,36,50,51,1,6,0,0,0,0,0,0,52,3,36,50,52,1,3,0,0,0,0,0,0,53,3,36,50,53,1,7,0,0,0,0,0,0,54,5,36,50,54,39,51,1,16,0,0,0,0,0,0,55,5,36,50,54,39,50,1,16,0,0,0,0,0,0]
theorem C18_6p0bound : C18_6p0.all wordBound = true := (by decide : [48,5,36,50,49,39,49,1,16,0,0,0,0,0,0,49,5,36,50,49,39,48,1,16,0,0,0,0,0,0,50,3,36,50,50,1,7,0,0,0,0,0,0,51,3,36,50,51,1,6,0,0,0,0,0,0,52,3,36,50,52,1,3,0,0,0,0,0,0,53,3,36,50,53,1,7,0,0,0,0,0,0,54,5,36,50,54,39,51,1,16,0,0,0,0,0,0,55,5,36,50,54,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C18_6words : List Nat := C18_6p0

theorem C18_6wire : C18_6.flatMap columnWords = C18_6words := by
  rfl

theorem C18_6wordBound : C18_6words.all wordBound = true := by
  simp only [C18_6words,List.all_append,C18_6p0bound]
  try rfl

theorem C18_6bounded : ∀ n ∈ C18_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_6wordBound

theorem C18_6length : C18_6.length = 8 := by rfl

def C18_7 : List Column := [⟨56, [36,50,54,39,49], (some (16)), false, false, false⟩,⟨57, [36,50,54,39,48], (some (16)), false, false, false⟩,⟨58, [36,50,55,39,51], (some (16)), false, false, false⟩,⟨59, [36,50,55,39,50], (some (16)), false, false, false⟩,⟨60, [36,50,55,39,49], (some (16)), false, false, false⟩,⟨61, [36,50,55,39,48], (some (16)), false, false, false⟩,⟨62, [36,50,56], (some (7)), false, false, false⟩,⟨63, [36,50,57], (some (6)), false, false, false⟩]

def C18_7p0 : List Nat := [56,5,36,50,54,39,49,1,16,0,0,0,0,0,0,57,5,36,50,54,39,48,1,16,0,0,0,0,0,0,58,5,36,50,55,39,51,1,16,0,0,0,0,0,0,59,5,36,50,55,39,50,1,16,0,0,0,0,0,0,60,5,36,50,55,39,49,1,16,0,0,0,0,0,0,61,5,36,50,55,39,48,1,16,0,0,0,0,0,0,62,3,36,50,56,1,7,0,0,0,0,0,0,63,3,36,50,57,1,6,0,0,0,0,0,0]
theorem C18_7p0bound : C18_7p0.all wordBound = true := (by decide : [56,5,36,50,54,39,49,1,16,0,0,0,0,0,0,57,5,36,50,54,39,48,1,16,0,0,0,0,0,0,58,5,36,50,55,39,51,1,16,0,0,0,0,0,0,59,5,36,50,55,39,50,1,16,0,0,0,0,0,0,60,5,36,50,55,39,49,1,16,0,0,0,0,0,0,61,5,36,50,55,39,48,1,16,0,0,0,0,0,0,62,3,36,50,56,1,7,0,0,0,0,0,0,63,3,36,50,57,1,6,0,0,0,0,0,0].all wordBound = true)

def C18_7words : List Nat := C18_7p0

theorem C18_7wire : C18_7.flatMap columnWords = C18_7words := by
  rfl

theorem C18_7wordBound : C18_7words.all wordBound = true := by
  simp only [C18_7words,List.all_append,C18_7p0bound]
  try rfl

theorem C18_7bounded : ∀ n ∈ C18_7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_7wordBound

theorem C18_7length : C18_7.length = 8 := by rfl

def C18_8 : List Column := [⟨64, [36,51,48], (some (3)), false, false, false⟩,⟨65, [108,99,109,36,51,49], (some (3)), false, false, false⟩,⟨66, [108,99,109,36,51,50], (some (1)), false, false, false⟩,⟨67, [115,116,97,109,112,36,51,53,39,49], (some (16)), false, false, false⟩,⟨68, [115,116,97,109,112,36,51,53,39,48], (some (16)), false, false, false⟩,⟨69, [115,116,97,109,112,36,51,54,39,49], (some (16)), false, false, false⟩,⟨70, [115,116,97,109,112,36,51,54,39,48], (some (16)), false, false, false⟩,⟨71, [115,116,97,109,112,36,51,55,39,49], (some (16)), false, false, false⟩]

def C18_8p0 : List Nat := [64,3,36,51,48,1,3,0,0,0,0,0,0,65,6,108,99,109,36,51,49,1,3,0,0,0,0,0,0,66,6,108,99,109,36,51,50,1,1,0,0,0,0,0,0,67,10,115,116,97,109,112,36,51,53,39,49,1,16,0,0,0,0,0,0,68,10,115,116,97,109,112,36,51,53,39,48,1,16,0,0,0,0,0,0,69,10,115,116,97,109,112,36,51,54,39,49,1,16,0,0,0,0,0,0,70,10,115,116,97,109,112,36,51,54,39,48,1,16,0,0,0,0,0,0,71,10,115]
theorem C18_8p0bound : C18_8p0.all wordBound = true := (by decide : [64,3,36,51,48,1,3,0,0,0,0,0,0,65,6,108,99,109,36,51,49,1,3,0,0,0,0,0,0,66,6,108,99,109,36,51,50,1,1,0,0,0,0,0,0,67,10,115,116,97,109,112,36,51,53,39,49,1,16,0,0,0,0,0,0,68,10,115,116,97,109,112,36,51,53,39,48,1,16,0,0,0,0,0,0,69,10,115,116,97,109,112,36,51,54,39,49,1,16,0,0,0,0,0,0,70,10,115,116,97,109,112,36,51,54,39,48,1,16,0,0,0,0,0,0,71,10,115].all wordBound = true)

def C18_8p1 : List Nat := [116,97,109,112,36,51,55,39,49,1,16,0,0,0,0,0,0]
theorem C18_8p1bound : C18_8p1.all wordBound = true := (by decide : [116,97,109,112,36,51,55,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C18_8words : List Nat := C18_8p0 ++ C18_8p1

theorem C18_8wire : C18_8.flatMap columnWords = C18_8words := by
  rfl

theorem C18_8wordBound : C18_8words.all wordBound = true := by
  simp only [C18_8words,List.all_append,C18_8p0bound,C18_8p1bound]
  try rfl

theorem C18_8bounded : ∀ n ∈ C18_8words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_8wordBound

theorem C18_8length : C18_8.length = 8 := by rfl

def C18_9 : List Column := [⟨72, [115,116,97,109,112,36,51,55,39,48], (some (16)), false, false, false⟩,⟨73, [115,116,97,109,112,36,51,56,39,49], (some (16)), false, false, false⟩,⟨74, [115,116,97,109,112,36,51,56,39,48], (some (16)), false, false, false⟩,⟨75, [115,116,97,109,112,36,51,57,39,49], (some (16)), false, false, false⟩,⟨76, [115,116,97,109,112,36,51,57,39,48], (some (16)), false, false, false⟩,⟨77, [115,116,97,109,112,36,52,48,39,49], (some (16)), false, false, false⟩,⟨78, [115,116,97,109,112,36,52,48,39,48], (some (16)), false, false, false⟩,⟨79, [115,116,97,109,112,36,52,49,39,49], (some (16)), false, false, false⟩]

def C18_9p0 : List Nat := [72,10,115,116,97,109,112,36,51,55,39,48,1,16,0,0,0,0,0,0,73,10,115,116,97,109,112,36,51,56,39,49,1,16,0,0,0,0,0,0,74,10,115,116,97,109,112,36,51,56,39,48,1,16,0,0,0,0,0,0,75,10,115,116,97,109,112,36,51,57,39,49,1,16,0,0,0,0,0,0,76,10,115,116,97,109,112,36,51,57,39,48,1,16,0,0,0,0,0,0,77,10,115,116,97,109,112,36,52,48,39,49,1,16,0,0,0,0,0,0,78,10,115,116,97,109,112,36]
theorem C18_9p0bound : C18_9p0.all wordBound = true := (by decide : [72,10,115,116,97,109,112,36,51,55,39,48,1,16,0,0,0,0,0,0,73,10,115,116,97,109,112,36,51,56,39,49,1,16,0,0,0,0,0,0,74,10,115,116,97,109,112,36,51,56,39,48,1,16,0,0,0,0,0,0,75,10,115,116,97,109,112,36,51,57,39,49,1,16,0,0,0,0,0,0,76,10,115,116,97,109,112,36,51,57,39,48,1,16,0,0,0,0,0,0,77,10,115,116,97,109,112,36,52,48,39,49,1,16,0,0,0,0,0,0,78,10,115,116,97,109,112,36].all wordBound = true)

def C18_9p1 : List Nat := [52,48,39,48,1,16,0,0,0,0,0,0,79,10,115,116,97,109,112,36,52,49,39,49,1,16,0,0,0,0,0,0]
theorem C18_9p1bound : C18_9p1.all wordBound = true := (by decide : [52,48,39,48,1,16,0,0,0,0,0,0,79,10,115,116,97,109,112,36,52,49,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C18_9words : List Nat := C18_9p0 ++ C18_9p1

theorem C18_9wire : C18_9.flatMap columnWords = C18_9words := by
  rfl

theorem C18_9wordBound : C18_9words.all wordBound = true := by
  simp only [C18_9words,List.all_append,C18_9p0bound,C18_9p1bound]
  try rfl

theorem C18_9bounded : ∀ n ∈ C18_9words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_9wordBound

theorem C18_9length : C18_9.length = 8 := by rfl

def C18_10 : List Column := [⟨80, [115,116,97,109,112,36,52,49,39,48], (some (16)), false, false, false⟩,⟨81, [115,116,97,109,112,36,52,50,39,49], (some (16)), false, false, false⟩,⟨82, [115,116,97,109,112,36,52,50,39,48], (some (16)), false, false, false⟩,⟨83, [115,116,97,109,112,36,52,51,39,49], (some (16)), false, false, false⟩,⟨84, [115,116,97,109,112,36,52,51,39,48], (some (16)), false, false, false⟩,⟨85, [99,36,49,48,51], (some (1)), false, false, false⟩,⟨86, [99,36,49,48,52], (some (1)), false, false, false⟩,⟨87, [99,36,49,48,53], (some (1)), false, false, false⟩]

def C18_10p0 : List Nat := [80,10,115,116,97,109,112,36,52,49,39,48,1,16,0,0,0,0,0,0,81,10,115,116,97,109,112,36,52,50,39,49,1,16,0,0,0,0,0,0,82,10,115,116,97,109,112,36,52,50,39,48,1,16,0,0,0,0,0,0,83,10,115,116,97,109,112,36,52,51,39,49,1,16,0,0,0,0,0,0,84,10,115,116,97,109,112,36,52,51,39,48,1,16,0,0,0,0,0,0,85,5,99,36,49,48,51,1,1,0,0,0,0,0,0,86,5,99,36,49,48,52,1,1,0,0,0,0]
theorem C18_10p0bound : C18_10p0.all wordBound = true := (by decide : [80,10,115,116,97,109,112,36,52,49,39,48,1,16,0,0,0,0,0,0,81,10,115,116,97,109,112,36,52,50,39,49,1,16,0,0,0,0,0,0,82,10,115,116,97,109,112,36,52,50,39,48,1,16,0,0,0,0,0,0,83,10,115,116,97,109,112,36,52,51,39,49,1,16,0,0,0,0,0,0,84,10,115,116,97,109,112,36,52,51,39,48,1,16,0,0,0,0,0,0,85,5,99,36,49,48,51,1,1,0,0,0,0,0,0,86,5,99,36,49,48,52,1,1,0,0,0,0].all wordBound = true)

def C18_10p1 : List Nat := [0,0,87,5,99,36,49,48,53,1,1,0,0,0,0,0,0]
theorem C18_10p1bound : C18_10p1.all wordBound = true := (by decide : [0,0,87,5,99,36,49,48,53,1,1,0,0,0,0,0,0].all wordBound = true)

def C18_10words : List Nat := C18_10p0 ++ C18_10p1

theorem C18_10wire : C18_10.flatMap columnWords = C18_10words := by
  rfl

theorem C18_10wordBound : C18_10words.all wordBound = true := by
  simp only [C18_10words,List.all_append,C18_10p0bound,C18_10p1bound]
  try rfl

theorem C18_10bounded : ∀ n ∈ C18_10words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_10wordBound

theorem C18_10length : C18_10.length = 8 := by rfl

def C18_11 : List Column := [⟨88, [99,36,49,48,54], (some (1)), false, false, false⟩,⟨89, [99,36,49,48,55], (some (1)), false, false, false⟩,⟨90, [99,36,49,48,56], (some (1)), false, false, false⟩,⟨91, [99,36,49,48,57], (some (1)), false, false, false⟩,⟨92, [99,36,49,49,48], (some (1)), false, false, false⟩,⟨93, [99,36,49,49,49], (some (1)), false, false, false⟩,⟨94, [99,36,49,49,50], (some (1)), false, false, false⟩,⟨95, [102,108,97,36,57,53], (some (16)), false, false, false⟩]

def C18_11p0 : List Nat := [88,5,99,36,49,48,54,1,1,0,0,0,0,0,0,89,5,99,36,49,48,55,1,1,0,0,0,0,0,0,90,5,99,36,49,48,56,1,1,0,0,0,0,0,0,91,5,99,36,49,48,57,1,1,0,0,0,0,0,0,92,5,99,36,49,49,48,1,1,0,0,0,0,0,0,93,5,99,36,49,49,49,1,1,0,0,0,0,0,0,94,5,99,36,49,49,50,1,1,0,0,0,0,0,0,95,6,102,108,97,36,57,53,1,16,0,0,0,0,0,0]
theorem C18_11p0bound : C18_11p0.all wordBound = true := (by decide : [88,5,99,36,49,48,54,1,1,0,0,0,0,0,0,89,5,99,36,49,48,55,1,1,0,0,0,0,0,0,90,5,99,36,49,48,56,1,1,0,0,0,0,0,0,91,5,99,36,49,48,57,1,1,0,0,0,0,0,0,92,5,99,36,49,49,48,1,1,0,0,0,0,0,0,93,5,99,36,49,49,49,1,1,0,0,0,0,0,0,94,5,99,36,49,49,50,1,1,0,0,0,0,0,0,95,6,102,108,97,36,57,53,1,16,0,0,0,0,0,0].all wordBound = true)

def C18_11words : List Nat := C18_11p0

theorem C18_11wire : C18_11.flatMap columnWords = C18_11words := by
  rfl

theorem C18_11wordBound : C18_11words.all wordBound = true := by
  simp only [C18_11words,List.all_append,C18_11p0bound]
  try rfl

theorem C18_11bounded : ∀ n ∈ C18_11words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_11wordBound

theorem C18_11length : C18_11.length = 8 := by rfl

def C18_12 : List Column := [⟨96, [102,108,97,36,57,54], (some (16)), false, false, false⟩,⟨97, [36,114,101,116], (some (1)), false, false, false⟩,⟨98, [36,112,99], (some (2)), false, false, false⟩,⟨99, [36,105,115,95,112,99,95,49], (some (1)), false, false, false⟩,⟨100, [36,105,115,95,112,99,95,50], (some (1)), false, false, false⟩,⟨101, [36,108,111,111,107,117,112,95,115,101,108,95,49,48,49], (some (1)), false, false, false⟩,⟨102, [36,108,111,111,107,117,112,95,115,101,108,95,49,48,50], (some (1)), false, false, false⟩,⟨103, [40,105,110,118,32,107,101,99,95,114,104,111,58,36,112,99,41], none, false, false, true⟩]

def C18_12p0 : List Nat := [96,6,102,108,97,36,57,54,1,16,0,0,0,0,0,0,97,4,36,114,101,116,1,1,0,0,0,0,0,0,98,3,36,112,99,1,2,0,0,0,0,0,0,99,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,100,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,101,15,36,108,111,111,107,117,112,95,115,101,108,95,49,48,49,1,1,0,0,0,0,0,0,102,15,36,108,111,111,107,117,112,95,115,101,108,95,49,48,50,1,1,0,0,0,0,0]
theorem C18_12p0bound : C18_12p0.all wordBound = true := (by decide : [96,6,102,108,97,36,57,54,1,16,0,0,0,0,0,0,97,4,36,114,101,116,1,1,0,0,0,0,0,0,98,3,36,112,99,1,2,0,0,0,0,0,0,99,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,100,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,101,15,36,108,111,111,107,117,112,95,115,101,108,95,49,48,49,1,1,0,0,0,0,0,0,102,15,36,108,111,111,107,117,112,95,115,101,108,95,49,48,50,1,1,0,0,0,0,0].all wordBound = true)

def C18_12p1 : List Nat := [0,103,17,40,105,110,118,32,107,101,99,95,114,104,111,58,36,112,99,41,0,0,0,0,0,0,1,0]
theorem C18_12p1bound : C18_12p1.all wordBound = true := (by decide : [0,103,17,40,105,110,118,32,107,101,99,95,114,104,111,58,36,112,99,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C18_12words : List Nat := C18_12p0 ++ C18_12p1

theorem C18_12wire : C18_12.flatMap columnWords = C18_12words := by
  rfl

theorem C18_12wordBound : C18_12words.all wordBound = true := by
  simp only [C18_12words,List.all_append,C18_12p0bound,C18_12p1bound]
  try rfl

theorem C18_12bounded : ∀ n ∈ C18_12words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C18_12wordBound

theorem C18_12length : C18_12.length = 8 := by rfl

def M18 : Module := ⟨18, [107,101,99,95,114,104,111], false, false, C18_0 ++ C18_1 ++ C18_2 ++ C18_3 ++ C18_4 ++ C18_5 ++ C18_6 ++ C18_7 ++ C18_8 ++ C18_9 ++ C18_10 ++ C18_11 ++ C18_12, ((List.range 0).map (fun n => [n]))⟩

def M18prefix : List Nat := [18,7,107,101,99,95,114,104,111,0,0,0,0,104]
theorem M18prefixwordBound : M18prefix.all wordBound = true := by decide

def M18words : List Nat := M18prefix ++ C18_0words ++ C18_1words ++ C18_2words ++ C18_3words ++ C18_4words ++ C18_5words ++ C18_6words ++ C18_7words ++ C18_8words ++ C18_9words ++ C18_10words ++ C18_11words ++ C18_12words ++ [0]

theorem M18wire : module.encode M18 = M18words := by
  rw [module_fast]
  simp only [M18,moduleWords,List.length_append,List.flatMap_append,C18_0length,C18_1length,C18_2length,C18_3length,C18_4length,C18_5length,C18_6length,C18_7length,C18_8length,C18_9length,C18_10length,C18_11length,C18_12length,C18_0wire,C18_1wire,C18_2wire,C18_3wire,C18_4wire,C18_5wire,C18_6wire,C18_7wire,C18_8wire,C18_9wire,C18_10wire,C18_11wire,C18_12wire]
  rfl

theorem M18wordBound : M18words.all wordBound = true := by
  simp only [M18words,List.all_append,M18prefixwordBound,C18_0wordBound,C18_1wordBound,C18_2wordBound,C18_3wordBound,C18_4wordBound,C18_5wordBound,C18_6wordBound,C18_7wordBound,C18_8wordBound,C18_9wordBound,C18_10wordBound,C18_11wordBound,C18_12wordBound]
  decide

theorem M18bounded : ∀ n ∈ M18words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M18wordBound

end DivRemFV.Replay
