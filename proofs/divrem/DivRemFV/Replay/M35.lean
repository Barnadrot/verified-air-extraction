import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C35_0 : List Column := [⟨0, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨3, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨4, [120,48], none, false, false, true⟩,⟨5, [120,49], none, false, false, true⟩,⟨6, [120,50], none, false, false, true⟩,⟨7, [120,51], none, false, false, true⟩]

def C35_0p0 : List Nat := [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111]
theorem C35_0p0bound : C35_0p0.all wordBound = true := (by decide : [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111].all wordBound = true)

def C35_0p1 : List Nat := [117,116,39,48,1,16,0,0,1,0,0,0,4,2,120,48,0,0,0,0,0,0,1,0,5,2,120,49,0,0,0,0,0,0,1,0,6,2,120,50,0,0,0,0,0,0,1,0,7,2,120,51,0,0,0,0,0,0,1,0]
theorem C35_0p1bound : C35_0p1.all wordBound = true := (by decide : [117,116,39,48,1,16,0,0,1,0,0,0,4,2,120,48,0,0,0,0,0,0,1,0,5,2,120,49,0,0,0,0,0,0,1,0,6,2,120,50,0,0,0,0,0,0,1,0,7,2,120,51,0,0,0,0,0,0,1,0].all wordBound = true)

def C35_0words : List Nat := C35_0p0 ++ C35_0p1

theorem C35_0wire : C35_0.flatMap columnWords = C35_0words := by
  rfl

theorem C35_0wordBound : C35_0words.all wordBound = true := by
  simp only [C35_0words,List.all_append,C35_0p0bound,C35_0p1bound]
  try rfl

theorem C35_0bounded : ∀ n ∈ C35_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C35_0wordBound

theorem C35_0length : C35_0.length = 8 := by rfl

def C35_1 : List Column := [⟨8, [116,48,49], none, false, false, true⟩,⟨9, [116,50,51], none, false, false, true⟩,⟨10, [116,48,49,50,51], none, false, false, true⟩,⟨11, [116,48,49,49,50,51], none, false, false, true⟩,⟨12, [116,48,49,50,51,51], none, false, false, true⟩,⟨13, [111], (some (5)), false, false, false⟩,⟨14, [99], (some (5)), false, false, false⟩,⟨15, [36,49,49], (some (5)), false, false, false⟩]

def C35_1p0 : List Nat := [8,3,116,48,49,0,0,0,0,0,0,1,0,9,3,116,50,51,0,0,0,0,0,0,1,0,10,5,116,48,49,50,51,0,0,0,0,0,0,1,0,11,6,116,48,49,49,50,51,0,0,0,0,0,0,1,0,12,6,116,48,49,50,51,51,0,0,0,0,0,0,1,0,13,1,111,1,5,0,0,0,0,0,0,14,1,99,1,5,0,0,0,0,0,0,15,3,36,49,49,1,5,0,0,0,0,0,0]
theorem C35_1p0bound : C35_1p0.all wordBound = true := (by decide : [8,3,116,48,49,0,0,0,0,0,0,1,0,9,3,116,50,51,0,0,0,0,0,0,1,0,10,5,116,48,49,50,51,0,0,0,0,0,0,1,0,11,6,116,48,49,49,50,51,0,0,0,0,0,0,1,0,12,6,116,48,49,50,51,51,0,0,0,0,0,0,1,0,13,1,111,1,5,0,0,0,0,0,0,14,1,99,1,5,0,0,0,0,0,0,15,3,36,49,49,1,5,0,0,0,0,0,0].all wordBound = true)

def C35_1words : List Nat := C35_1p0

theorem C35_1wire : C35_1.flatMap columnWords = C35_1words := by
  rfl

theorem C35_1wordBound : C35_1words.all wordBound = true := by
  simp only [C35_1words,List.all_append,C35_1p0bound]
  try rfl

theorem C35_1bounded : ∀ n ∈ C35_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C35_1wordBound

theorem C35_1length : C35_1.length = 8 := by rfl

def C35_2 : List Column := [⟨16, [36,49,50], (some (5)), false, false, false⟩,⟨17, [36,49,51], (some (5)), false, false, false⟩,⟨18, [36,49,52], (some (5)), false, false, false⟩,⟨19, [36,49,53], (some (5)), false, false, false⟩,⟨20, [36,49,54], none, false, false, true⟩,⟨21, [36,49,55], none, false, false, true⟩,⟨22, [36,49,56], (some (5)), false, false, false⟩,⟨23, [36,49,57], none, false, false, true⟩]

def C35_2p0 : List Nat := [16,3,36,49,50,1,5,0,0,0,0,0,0,17,3,36,49,51,1,5,0,0,0,0,0,0,18,3,36,49,52,1,5,0,0,0,0,0,0,19,3,36,49,53,1,5,0,0,0,0,0,0,20,3,36,49,54,0,0,0,0,0,0,1,0,21,3,36,49,55,0,0,0,0,0,0,1,0,22,3,36,49,56,1,5,0,0,0,0,0,0,23,3,36,49,57,0,0,0,0,0,0,1,0]
theorem C35_2p0bound : C35_2p0.all wordBound = true := (by decide : [16,3,36,49,50,1,5,0,0,0,0,0,0,17,3,36,49,51,1,5,0,0,0,0,0,0,18,3,36,49,52,1,5,0,0,0,0,0,0,19,3,36,49,53,1,5,0,0,0,0,0,0,20,3,36,49,54,0,0,0,0,0,0,1,0,21,3,36,49,55,0,0,0,0,0,0,1,0,22,3,36,49,56,1,5,0,0,0,0,0,0,23,3,36,49,57,0,0,0,0,0,0,1,0].all wordBound = true)

def C35_2words : List Nat := C35_2p0

theorem C35_2wire : C35_2.flatMap columnWords = C35_2words := by
  rfl

theorem C35_2wordBound : C35_2words.all wordBound = true := by
  simp only [C35_2words,List.all_append,C35_2p0bound]
  try rfl

theorem C35_2bounded : ∀ n ∈ C35_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C35_2wordBound

theorem C35_2length : C35_2.length = 8 := by rfl

def C35_3 : List Column := [⟨24, [36,50,48], none, false, false, true⟩,⟨25, [36,50,49], (some (5)), false, false, false⟩,⟨26, [36,50,50], none, false, false, true⟩,⟨27, [36,50,51], (some (5)), false, false, false⟩,⟨28, [36,50,52], none, false, false, true⟩,⟨29, [108,99,109,36,50,53], (some (5)), false, false, false⟩,⟨30, [108,99,109,36,50,54], (some (1)), false, false, false⟩,⟨31, [115,116,97,109,112,36,50,57,39,49], (some (16)), false, false, false⟩]

def C35_3p0 : List Nat := [24,3,36,50,48,0,0,0,0,0,0,1,0,25,3,36,50,49,1,5,0,0,0,0,0,0,26,3,36,50,50,0,0,0,0,0,0,1,0,27,3,36,50,51,1,5,0,0,0,0,0,0,28,3,36,50,52,0,0,0,0,0,0,1,0,29,6,108,99,109,36,50,53,1,5,0,0,0,0,0,0,30,6,108,99,109,36,50,54,1,1,0,0,0,0,0,0,31,10,115,116,97,109,112,36,50,57,39,49,1,16,0,0,0,0,0,0]
theorem C35_3p0bound : C35_3p0.all wordBound = true := (by decide : [24,3,36,50,48,0,0,0,0,0,0,1,0,25,3,36,50,49,1,5,0,0,0,0,0,0,26,3,36,50,50,0,0,0,0,0,0,1,0,27,3,36,50,51,1,5,0,0,0,0,0,0,28,3,36,50,52,0,0,0,0,0,0,1,0,29,6,108,99,109,36,50,53,1,5,0,0,0,0,0,0,30,6,108,99,109,36,50,54,1,1,0,0,0,0,0,0,31,10,115,116,97,109,112,36,50,57,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C35_3words : List Nat := C35_3p0

theorem C35_3wire : C35_3.flatMap columnWords = C35_3words := by
  rfl

theorem C35_3wordBound : C35_3words.all wordBound = true := by
  simp only [C35_3words,List.all_append,C35_3p0bound]
  try rfl

theorem C35_3bounded : ∀ n ∈ C35_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C35_3wordBound

theorem C35_3length : C35_3.length = 8 := by rfl

def C35_4 : List Column := [⟨32, [115,116,97,109,112,36,50,57,39,48], (some (16)), false, false, false⟩,⟨33, [115,116,97,109,112,36,51,48,39,49], (some (16)), false, false, false⟩,⟨34, [115,116,97,109,112,36,51,48,39,48], (some (16)), false, false, false⟩,⟨35, [115,116,97,109,112,36,51,49,39,49], (some (16)), false, false, false⟩,⟨36, [115,116,97,109,112,36,51,49,39,48], (some (16)), false, false, false⟩,⟨37, [115,116,97,109,112,36,51,50,39,49], (some (16)), false, false, false⟩,⟨38, [115,116,97,109,112,36,51,50,39,48], (some (16)), false, false, false⟩,⟨39, [115,116,97,109,112,36,51,51,39,49], (some (16)), false, false, false⟩]

def C35_4p0 : List Nat := [32,10,115,116,97,109,112,36,50,57,39,48,1,16,0,0,0,0,0,0,33,10,115,116,97,109,112,36,51,48,39,49,1,16,0,0,0,0,0,0,34,10,115,116,97,109,112,36,51,48,39,48,1,16,0,0,0,0,0,0,35,10,115,116,97,109,112,36,51,49,39,49,1,16,0,0,0,0,0,0,36,10,115,116,97,109,112,36,51,49,39,48,1,16,0,0,0,0,0,0,37,10,115,116,97,109,112,36,51,50,39,49,1,16,0,0,0,0,0,0,38,10,115,116,97,109,112,36]
theorem C35_4p0bound : C35_4p0.all wordBound = true := (by decide : [32,10,115,116,97,109,112,36,50,57,39,48,1,16,0,0,0,0,0,0,33,10,115,116,97,109,112,36,51,48,39,49,1,16,0,0,0,0,0,0,34,10,115,116,97,109,112,36,51,48,39,48,1,16,0,0,0,0,0,0,35,10,115,116,97,109,112,36,51,49,39,49,1,16,0,0,0,0,0,0,36,10,115,116,97,109,112,36,51,49,39,48,1,16,0,0,0,0,0,0,37,10,115,116,97,109,112,36,51,50,39,49,1,16,0,0,0,0,0,0,38,10,115,116,97,109,112,36].all wordBound = true)

def C35_4p1 : List Nat := [51,50,39,48,1,16,0,0,0,0,0,0,39,10,115,116,97,109,112,36,51,51,39,49,1,16,0,0,0,0,0,0]
theorem C35_4p1bound : C35_4p1.all wordBound = true := (by decide : [51,50,39,48,1,16,0,0,0,0,0,0,39,10,115,116,97,109,112,36,51,51,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C35_4words : List Nat := C35_4p0 ++ C35_4p1

theorem C35_4wire : C35_4.flatMap columnWords = C35_4words := by
  rfl

theorem C35_4wordBound : C35_4words.all wordBound = true := by
  simp only [C35_4words,List.all_append,C35_4p0bound,C35_4p1bound]
  try rfl

theorem C35_4bounded : ∀ n ∈ C35_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C35_4wordBound

theorem C35_4length : C35_4.length = 8 := by rfl

def C35_5 : List Column := [⟨40, [115,116,97,109,112,36,51,51,39,48], (some (16)), false, false, false⟩,⟨41, [115,116,97,109,112,36,51,52,39,49], (some (16)), false, false, false⟩,⟨42, [115,116,97,109,112,36,51,52,39,48], (some (16)), false, false, false⟩,⟨43, [115,116,97,109,112,36,51,53,39,49], (some (16)), false, false, false⟩,⟨44, [115,116,97,109,112,36,51,53,39,48], (some (16)), false, false, false⟩,⟨45, [99,36,53,57], (some (1)), false, false, false⟩,⟨46, [99,36,54,48], (some (1)), false, false, false⟩,⟨47, [99,36,54,49], (some (1)), false, false, false⟩]

def C35_5p0 : List Nat := [40,10,115,116,97,109,112,36,51,51,39,48,1,16,0,0,0,0,0,0,41,10,115,116,97,109,112,36,51,52,39,49,1,16,0,0,0,0,0,0,42,10,115,116,97,109,112,36,51,52,39,48,1,16,0,0,0,0,0,0,43,10,115,116,97,109,112,36,51,53,39,49,1,16,0,0,0,0,0,0,44,10,115,116,97,109,112,36,51,53,39,48,1,16,0,0,0,0,0,0,45,4,99,36,53,57,1,1,0,0,0,0,0,0,46,4,99,36,54,48,1,1,0,0,0,0,0,0]
theorem C35_5p0bound : C35_5p0.all wordBound = true := (by decide : [40,10,115,116,97,109,112,36,51,51,39,48,1,16,0,0,0,0,0,0,41,10,115,116,97,109,112,36,51,52,39,49,1,16,0,0,0,0,0,0,42,10,115,116,97,109,112,36,51,52,39,48,1,16,0,0,0,0,0,0,43,10,115,116,97,109,112,36,51,53,39,49,1,16,0,0,0,0,0,0,44,10,115,116,97,109,112,36,51,53,39,48,1,16,0,0,0,0,0,0,45,4,99,36,53,57,1,1,0,0,0,0,0,0,46,4,99,36,54,48,1,1,0,0,0,0,0,0].all wordBound = true)

def C35_5p1 : List Nat := [47,4,99,36,54,49,1,1,0,0,0,0,0,0]
theorem C35_5p1bound : C35_5p1.all wordBound = true := (by decide : [47,4,99,36,54,49,1,1,0,0,0,0,0,0].all wordBound = true)

def C35_5words : List Nat := C35_5p0 ++ C35_5p1

theorem C35_5wire : C35_5.flatMap columnWords = C35_5words := by
  rfl

theorem C35_5wordBound : C35_5words.all wordBound = true := by
  simp only [C35_5words,List.all_append,C35_5p0bound,C35_5p1bound]
  try rfl

theorem C35_5bounded : ∀ n ∈ C35_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C35_5wordBound

theorem C35_5length : C35_5.length = 8 := by rfl

def C35_6 : List Column := [⟨48, [99,36,54,50], (some (1)), false, false, false⟩,⟨49, [99,36,54,51], (some (1)), false, false, false⟩,⟨50, [99,36,54,52], (some (1)), false, false, false⟩,⟨51, [99,36,54,53], (some (1)), false, false, false⟩,⟨52, [99,36,54,54], (some (1)), false, false, false⟩,⟨53, [102,108,97,36,53,51], (some (16)), false, false, false⟩,⟨54, [102,108,97,36,53,52], (some (16)), false, false, false⟩,⟨55, [36,114,101,116], (some (1)), false, false, false⟩]

def C35_6p0 : List Nat := [48,4,99,36,54,50,1,1,0,0,0,0,0,0,49,4,99,36,54,51,1,1,0,0,0,0,0,0,50,4,99,36,54,52,1,1,0,0,0,0,0,0,51,4,99,36,54,53,1,1,0,0,0,0,0,0,52,4,99,36,54,54,1,1,0,0,0,0,0,0,53,6,102,108,97,36,53,51,1,16,0,0,0,0,0,0,54,6,102,108,97,36,53,52,1,16,0,0,0,0,0,0,55,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C35_6p0bound : C35_6p0.all wordBound = true := (by decide : [48,4,99,36,54,50,1,1,0,0,0,0,0,0,49,4,99,36,54,51,1,1,0,0,0,0,0,0,50,4,99,36,54,52,1,1,0,0,0,0,0,0,51,4,99,36,54,53,1,1,0,0,0,0,0,0,52,4,99,36,54,54,1,1,0,0,0,0,0,0,53,6,102,108,97,36,53,51,1,16,0,0,0,0,0,0,54,6,102,108,97,36,53,52,1,16,0,0,0,0,0,0,55,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C35_6words : List Nat := C35_6p0

theorem C35_6wire : C35_6.flatMap columnWords = C35_6words := by
  rfl

theorem C35_6wordBound : C35_6words.all wordBound = true := by
  simp only [C35_6words,List.all_append,C35_6p0bound]
  try rfl

theorem C35_6bounded : ∀ n ∈ C35_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C35_6wordBound

theorem C35_6length : C35_6.length = 8 := by rfl

def C35_7 : List Column := [⟨56, [36,112,99], (some (2)), false, false, false⟩,⟨57, [36,105,115,95,112,99,95,49], (some (1)), false, false, false⟩,⟨58, [36,105,115,95,112,99,95,50], (some (1)), false, false, false⟩,⟨59, [36,108,111,111,107,117,112,95,115,101,108,95,53,57], (some (1)), false, false, false⟩,⟨60, [36,108,111,111,107,117,112,95,115,101,108,95,54,48], (some (1)), false, false, false⟩,⟨61, [40,105,110,118,32,109,97,116,95,109,117,108,95,109,52,58,36,112,99,41], none, false, false, true⟩]

def C35_7p0 : List Nat := [56,3,36,112,99,1,2,0,0,0,0,0,0,57,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,58,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,59,14,36,108,111,111,107,117,112,95,115,101,108,95,53,57,1,1,0,0,0,0,0,0,60,14,36,108,111,111,107,117,112,95,115,101,108,95,54,48,1,1,0,0,0,0,0,0,61,20,40,105,110,118,32,109,97,116,95,109,117,108,95,109,52,58,36,112,99,41,0,0,0,0,0,0,1,0]
theorem C35_7p0bound : C35_7p0.all wordBound = true := (by decide : [56,3,36,112,99,1,2,0,0,0,0,0,0,57,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,58,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,59,14,36,108,111,111,107,117,112,95,115,101,108,95,53,57,1,1,0,0,0,0,0,0,60,14,36,108,111,111,107,117,112,95,115,101,108,95,54,48,1,1,0,0,0,0,0,0,61,20,40,105,110,118,32,109,97,116,95,109,117,108,95,109,52,58,36,112,99,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C35_7words : List Nat := C35_7p0

theorem C35_7wire : C35_7.flatMap columnWords = C35_7words := by
  rfl

theorem C35_7wordBound : C35_7words.all wordBound = true := by
  simp only [C35_7words,List.all_append,C35_7p0bound]
  try rfl

theorem C35_7bounded : ∀ n ∈ C35_7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C35_7wordBound

theorem C35_7length : C35_7.length = 6 := by rfl

def M35 : Module := ⟨35, [109,97,116,95,109,117,108,95,109,52], false, false, C35_0 ++ C35_1 ++ C35_2 ++ C35_3 ++ C35_4 ++ C35_5 ++ C35_6 ++ C35_7, ((List.range 0).map (fun n => [n]))⟩

def M35prefix : List Nat := [35,10,109,97,116,95,109,117,108,95,109,52,0,0,0,0,62]
theorem M35prefixwordBound : M35prefix.all wordBound = true := by decide

def M35words : List Nat := M35prefix ++ C35_0words ++ C35_1words ++ C35_2words ++ C35_3words ++ C35_4words ++ C35_5words ++ C35_6words ++ C35_7words ++ [0]

theorem M35wire : module.encode M35 = M35words := by
  rw [module_fast]
  simp only [M35,moduleWords,List.length_append,List.flatMap_append,C35_0length,C35_1length,C35_2length,C35_3length,C35_4length,C35_5length,C35_6length,C35_7length,C35_0wire,C35_1wire,C35_2wire,C35_3wire,C35_4wire,C35_5wire,C35_6wire,C35_7wire]
  rfl

theorem M35wordBound : M35words.all wordBound = true := by
  simp only [M35words,List.all_append,M35prefixwordBound,C35_0wordBound,C35_1wordBound,C35_2wordBound,C35_3wordBound,C35_4wordBound,C35_5wordBound,C35_6wordBound,C35_7wordBound]
  decide

theorem M35bounded : ∀ n ∈ M35words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M35wordBound

end DivRemFV.Replay
