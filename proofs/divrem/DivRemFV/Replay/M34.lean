import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C34_0 : List Column := [⟨0, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨3, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨4, [115,48], none, false, false, true⟩,⟨5, [115,49], none, false, false, true⟩,⟨6, [115,50], none, false, false, true⟩,⟨7, [115,51], none, false, false, true⟩]

def C34_0p0 : List Nat := [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111]
theorem C34_0p0bound : C34_0p0.all wordBound = true := (by decide : [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111].all wordBound = true)

def C34_0p1 : List Nat := [117,116,39,48,1,16,0,0,1,0,0,0,4,2,115,48,0,0,0,0,0,0,1,0,5,2,115,49,0,0,0,0,0,0,1,0,6,2,115,50,0,0,0,0,0,0,1,0,7,2,115,51,0,0,0,0,0,0,1,0]
theorem C34_0p1bound : C34_0p1.all wordBound = true := (by decide : [117,116,39,48,1,16,0,0,1,0,0,0,4,2,115,48,0,0,0,0,0,0,1,0,5,2,115,49,0,0,0,0,0,0,1,0,6,2,115,50,0,0,0,0,0,0,1,0,7,2,115,51,0,0,0,0,0,0,1,0].all wordBound = true)

def C34_0words : List Nat := C34_0p0 ++ C34_0p1

theorem C34_0wire : C34_0.flatMap columnWords = C34_0words := by
  rfl

theorem C34_0wordBound : C34_0words.all wordBound = true := by
  simp only [C34_0words,List.all_append,C34_0p0bound,C34_0p1bound]
  try rfl

theorem C34_0bounded : ∀ n ∈ C34_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_0wordBound

theorem C34_0length : C34_0.length = 8 := by rfl

def C34_1 : List Column := [⟨8, [111], (some (5)), false, false, false⟩,⟨9, [99], (some (5)), false, false, false⟩,⟨10, [99,36,49], (some (5)), false, false, false⟩,⟨11, [36,55], none, false, false, true⟩,⟨12, [36,56], (some (5)), false, false, false⟩,⟨13, [36,57], none, false, false, true⟩,⟨14, [36,49,48], (some (5)), false, false, false⟩,⟨15, [36,49,49], none, false, false, true⟩]

def C34_1p0 : List Nat := [8,1,111,1,5,0,0,0,0,0,0,9,1,99,1,5,0,0,0,0,0,0,10,3,99,36,49,1,5,0,0,0,0,0,0,11,2,36,55,0,0,0,0,0,0,1,0,12,2,36,56,1,5,0,0,0,0,0,0,13,2,36,57,0,0,0,0,0,0,1,0,14,3,36,49,48,1,5,0,0,0,0,0,0,15,3,36,49,49,0,0,0,0,0,0,1,0]
theorem C34_1p0bound : C34_1p0.all wordBound = true := (by decide : [8,1,111,1,5,0,0,0,0,0,0,9,1,99,1,5,0,0,0,0,0,0,10,3,99,36,49,1,5,0,0,0,0,0,0,11,2,36,55,0,0,0,0,0,0,1,0,12,2,36,56,1,5,0,0,0,0,0,0,13,2,36,57,0,0,0,0,0,0,1,0,14,3,36,49,48,1,5,0,0,0,0,0,0,15,3,36,49,49,0,0,0,0,0,0,1,0].all wordBound = true)

def C34_1words : List Nat := C34_1p0

theorem C34_1wire : C34_1.flatMap columnWords = C34_1words := by
  rfl

theorem C34_1wordBound : C34_1words.all wordBound = true := by
  simp only [C34_1words,List.all_append,C34_1p0bound]
  try rfl

theorem C34_1bounded : ∀ n ∈ C34_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_1wordBound

theorem C34_1length : C34_1.length = 8 := by rfl

def C34_2 : List Column := [⟨16, [36,49,50], (some (5)), false, false, false⟩,⟨17, [36,49,51], none, false, false, true⟩,⟨18, [36,49,52], (some (5)), false, false, false⟩,⟨19, [36,49,53], (some (5)), false, false, false⟩,⟨20, [36,49,54], none, false, false, true⟩,⟨21, [36,49,55], none, false, false, true⟩,⟨22, [36,49,56], (some (5)), false, false, false⟩,⟨23, [36,49,57], (some (5)), false, false, false⟩]

def C34_2p0 : List Nat := [16,3,36,49,50,1,5,0,0,0,0,0,0,17,3,36,49,51,0,0,0,0,0,0,1,0,18,3,36,49,52,1,5,0,0,0,0,0,0,19,3,36,49,53,1,5,0,0,0,0,0,0,20,3,36,49,54,0,0,0,0,0,0,1,0,21,3,36,49,55,0,0,0,0,0,0,1,0,22,3,36,49,56,1,5,0,0,0,0,0,0,23,3,36,49,57,1,5,0,0,0,0,0,0]
theorem C34_2p0bound : C34_2p0.all wordBound = true := (by decide : [16,3,36,49,50,1,5,0,0,0,0,0,0,17,3,36,49,51,0,0,0,0,0,0,1,0,18,3,36,49,52,1,5,0,0,0,0,0,0,19,3,36,49,53,1,5,0,0,0,0,0,0,20,3,36,49,54,0,0,0,0,0,0,1,0,21,3,36,49,55,0,0,0,0,0,0,1,0,22,3,36,49,56,1,5,0,0,0,0,0,0,23,3,36,49,57,1,5,0,0,0,0,0,0].all wordBound = true)

def C34_2words : List Nat := C34_2p0

theorem C34_2wire : C34_2.flatMap columnWords = C34_2words := by
  rfl

theorem C34_2wordBound : C34_2words.all wordBound = true := by
  simp only [C34_2words,List.all_append,C34_2p0bound]
  try rfl

theorem C34_2bounded : ∀ n ∈ C34_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_2wordBound

theorem C34_2length : C34_2.length = 8 := by rfl

def C34_3 : List Column := [⟨24, [36,50,48], none, false, false, true⟩,⟨25, [36,50,49], none, false, false, true⟩,⟨26, [36,50,50], (some (5)), false, false, false⟩,⟨27, [36,50,51], (some (5)), false, false, false⟩,⟨28, [36,50,52], none, false, false, true⟩,⟨29, [36,50,53], none, false, false, true⟩,⟨30, [36,50,54], (some (5)), false, false, false⟩,⟨31, [36,50,55], (some (5)), false, false, false⟩]

def C34_3p0 : List Nat := [24,3,36,50,48,0,0,0,0,0,0,1,0,25,3,36,50,49,0,0,0,0,0,0,1,0,26,3,36,50,50,1,5,0,0,0,0,0,0,27,3,36,50,51,1,5,0,0,0,0,0,0,28,3,36,50,52,0,0,0,0,0,0,1,0,29,3,36,50,53,0,0,0,0,0,0,1,0,30,3,36,50,54,1,5,0,0,0,0,0,0,31,3,36,50,55,1,5,0,0,0,0,0,0]
theorem C34_3p0bound : C34_3p0.all wordBound = true := (by decide : [24,3,36,50,48,0,0,0,0,0,0,1,0,25,3,36,50,49,0,0,0,0,0,0,1,0,26,3,36,50,50,1,5,0,0,0,0,0,0,27,3,36,50,51,1,5,0,0,0,0,0,0,28,3,36,50,52,0,0,0,0,0,0,1,0,29,3,36,50,53,0,0,0,0,0,0,1,0,30,3,36,50,54,1,5,0,0,0,0,0,0,31,3,36,50,55,1,5,0,0,0,0,0,0].all wordBound = true)

def C34_3words : List Nat := C34_3p0

theorem C34_3wire : C34_3.flatMap columnWords = C34_3words := by
  rfl

theorem C34_3wordBound : C34_3words.all wordBound = true := by
  simp only [C34_3words,List.all_append,C34_3p0bound]
  try rfl

theorem C34_3bounded : ∀ n ∈ C34_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_3wordBound

theorem C34_3length : C34_3.length = 8 := by rfl

def C34_4 : List Column := [⟨32, [36,50,56], none, false, false, true⟩,⟨33, [36,50,57], none, false, false, true⟩,⟨34, [36,51,48], (some (5)), false, false, false⟩,⟨35, [108,99,109,36,51,49], (some (5)), false, false, false⟩,⟨36, [108,99,109,36,51,50], (some (1)), false, false, false⟩,⟨37, [108,99,109,36,51,51], (some (5)), false, false, false⟩,⟨38, [108,99,109,36,51,52], (some (1)), false, false, false⟩,⟨39, [115,116,97,109,112,36,51,55,39,49], (some (16)), false, false, false⟩]

def C34_4p0 : List Nat := [32,3,36,50,56,0,0,0,0,0,0,1,0,33,3,36,50,57,0,0,0,0,0,0,1,0,34,3,36,51,48,1,5,0,0,0,0,0,0,35,6,108,99,109,36,51,49,1,5,0,0,0,0,0,0,36,6,108,99,109,36,51,50,1,1,0,0,0,0,0,0,37,6,108,99,109,36,51,51,1,5,0,0,0,0,0,0,38,6,108,99,109,36,51,52,1,1,0,0,0,0,0,0,39,10,115,116,97,109,112,36,51,55,39,49,1,16,0,0,0,0,0,0]
theorem C34_4p0bound : C34_4p0.all wordBound = true := (by decide : [32,3,36,50,56,0,0,0,0,0,0,1,0,33,3,36,50,57,0,0,0,0,0,0,1,0,34,3,36,51,48,1,5,0,0,0,0,0,0,35,6,108,99,109,36,51,49,1,5,0,0,0,0,0,0,36,6,108,99,109,36,51,50,1,1,0,0,0,0,0,0,37,6,108,99,109,36,51,51,1,5,0,0,0,0,0,0,38,6,108,99,109,36,51,52,1,1,0,0,0,0,0,0,39,10,115,116,97,109,112,36,51,55,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C34_4words : List Nat := C34_4p0

theorem C34_4wire : C34_4.flatMap columnWords = C34_4words := by
  rfl

theorem C34_4wordBound : C34_4words.all wordBound = true := by
  simp only [C34_4words,List.all_append,C34_4p0bound]
  try rfl

theorem C34_4bounded : ∀ n ∈ C34_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_4wordBound

theorem C34_4length : C34_4.length = 8 := by rfl

def C34_5 : List Column := [⟨40, [115,116,97,109,112,36,51,55,39,48], (some (16)), false, false, false⟩,⟨41, [115,116,97,109,112,36,51,56,39,49], (some (16)), false, false, false⟩,⟨42, [115,116,97,109,112,36,51,56,39,48], (some (16)), false, false, false⟩,⟨43, [115,116,97,109,112,36,51,57,39,49], (some (16)), false, false, false⟩,⟨44, [115,116,97,109,112,36,51,57,39,48], (some (16)), false, false, false⟩,⟨45, [115,116,97,109,112,36,52,48,39,49], (some (16)), false, false, false⟩,⟨46, [115,116,97,109,112,36,52,48,39,48], (some (16)), false, false, false⟩,⟨47, [115,116,97,109,112,36,52,49,39,49], (some (16)), false, false, false⟩]

def C34_5p0 : List Nat := [40,10,115,116,97,109,112,36,51,55,39,48,1,16,0,0,0,0,0,0,41,10,115,116,97,109,112,36,51,56,39,49,1,16,0,0,0,0,0,0,42,10,115,116,97,109,112,36,51,56,39,48,1,16,0,0,0,0,0,0,43,10,115,116,97,109,112,36,51,57,39,49,1,16,0,0,0,0,0,0,44,10,115,116,97,109,112,36,51,57,39,48,1,16,0,0,0,0,0,0,45,10,115,116,97,109,112,36,52,48,39,49,1,16,0,0,0,0,0,0,46,10,115,116,97,109,112,36]
theorem C34_5p0bound : C34_5p0.all wordBound = true := (by decide : [40,10,115,116,97,109,112,36,51,55,39,48,1,16,0,0,0,0,0,0,41,10,115,116,97,109,112,36,51,56,39,49,1,16,0,0,0,0,0,0,42,10,115,116,97,109,112,36,51,56,39,48,1,16,0,0,0,0,0,0,43,10,115,116,97,109,112,36,51,57,39,49,1,16,0,0,0,0,0,0,44,10,115,116,97,109,112,36,51,57,39,48,1,16,0,0,0,0,0,0,45,10,115,116,97,109,112,36,52,48,39,49,1,16,0,0,0,0,0,0,46,10,115,116,97,109,112,36].all wordBound = true)

def C34_5p1 : List Nat := [52,48,39,48,1,16,0,0,0,0,0,0,47,10,115,116,97,109,112,36,52,49,39,49,1,16,0,0,0,0,0,0]
theorem C34_5p1bound : C34_5p1.all wordBound = true := (by decide : [52,48,39,48,1,16,0,0,0,0,0,0,47,10,115,116,97,109,112,36,52,49,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C34_5words : List Nat := C34_5p0 ++ C34_5p1

theorem C34_5wire : C34_5.flatMap columnWords = C34_5words := by
  rfl

theorem C34_5wordBound : C34_5words.all wordBound = true := by
  simp only [C34_5words,List.all_append,C34_5p0bound,C34_5p1bound]
  try rfl

theorem C34_5bounded : ∀ n ∈ C34_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_5wordBound

theorem C34_5length : C34_5.length = 8 := by rfl

def C34_6 : List Column := [⟨48, [115,116,97,109,112,36,52,49,39,48], (some (16)), false, false, false⟩,⟨49, [115,116,97,109,112,36,52,50,39,49], (some (16)), false, false, false⟩,⟨50, [115,116,97,109,112,36,52,50,39,48], (some (16)), false, false, false⟩,⟨51, [115,116,97,109,112,36,52,51,39,49], (some (16)), false, false, false⟩,⟨52, [115,116,97,109,112,36,52,51,39,48], (some (16)), false, false, false⟩,⟨53, [115,116,97,109,112,36,52,52,39,49], (some (16)), false, false, false⟩,⟨54, [115,116,97,109,112,36,52,52,39,48], (some (16)), false, false, false⟩,⟨55, [115,116,97,109,112,36,53,51,39,49], (some (16)), false, false, false⟩]

def C34_6p0 : List Nat := [48,10,115,116,97,109,112,36,52,49,39,48,1,16,0,0,0,0,0,0,49,10,115,116,97,109,112,36,52,50,39,49,1,16,0,0,0,0,0,0,50,10,115,116,97,109,112,36,52,50,39,48,1,16,0,0,0,0,0,0,51,10,115,116,97,109,112,36,52,51,39,49,1,16,0,0,0,0,0,0,52,10,115,116,97,109,112,36,52,51,39,48,1,16,0,0,0,0,0,0,53,10,115,116,97,109,112,36,52,52,39,49,1,16,0,0,0,0,0,0,54,10,115,116,97,109,112,36]
theorem C34_6p0bound : C34_6p0.all wordBound = true := (by decide : [48,10,115,116,97,109,112,36,52,49,39,48,1,16,0,0,0,0,0,0,49,10,115,116,97,109,112,36,52,50,39,49,1,16,0,0,0,0,0,0,50,10,115,116,97,109,112,36,52,50,39,48,1,16,0,0,0,0,0,0,51,10,115,116,97,109,112,36,52,51,39,49,1,16,0,0,0,0,0,0,52,10,115,116,97,109,112,36,52,51,39,48,1,16,0,0,0,0,0,0,53,10,115,116,97,109,112,36,52,52,39,49,1,16,0,0,0,0,0,0,54,10,115,116,97,109,112,36].all wordBound = true)

def C34_6p1 : List Nat := [52,52,39,48,1,16,0,0,0,0,0,0,55,10,115,116,97,109,112,36,53,51,39,49,1,16,0,0,0,0,0,0]
theorem C34_6p1bound : C34_6p1.all wordBound = true := (by decide : [52,52,39,48,1,16,0,0,0,0,0,0,55,10,115,116,97,109,112,36,53,51,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C34_6words : List Nat := C34_6p0 ++ C34_6p1

theorem C34_6wire : C34_6.flatMap columnWords = C34_6words := by
  rfl

theorem C34_6wordBound : C34_6words.all wordBound = true := by
  simp only [C34_6words,List.all_append,C34_6p0bound,C34_6p1bound]
  try rfl

theorem C34_6bounded : ∀ n ∈ C34_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_6wordBound

theorem C34_6length : C34_6.length = 8 := by rfl

def C34_7 : List Column := [⟨56, [115,116,97,109,112,36,53,51,39,48], (some (16)), false, false, false⟩,⟨57, [115,116,97,109,112,36,53,52,39,49], (some (16)), false, false, false⟩,⟨58, [115,116,97,109,112,36,53,52,39,48], (some (16)), false, false, false⟩,⟨59, [115,116,97,109,112,36,53,53,39,49], (some (16)), false, false, false⟩,⟨60, [115,116,97,109,112,36,53,53,39,48], (some (16)), false, false, false⟩,⟨61, [99,36,57,49], (some (1)), false, false, false⟩,⟨62, [99,36,57,50], (some (1)), false, false, false⟩,⟨63, [99,36,57,51], (some (1)), false, false, false⟩]

def C34_7p0 : List Nat := [56,10,115,116,97,109,112,36,53,51,39,48,1,16,0,0,0,0,0,0,57,10,115,116,97,109,112,36,53,52,39,49,1,16,0,0,0,0,0,0,58,10,115,116,97,109,112,36,53,52,39,48,1,16,0,0,0,0,0,0,59,10,115,116,97,109,112,36,53,53,39,49,1,16,0,0,0,0,0,0,60,10,115,116,97,109,112,36,53,53,39,48,1,16,0,0,0,0,0,0,61,4,99,36,57,49,1,1,0,0,0,0,0,0,62,4,99,36,57,50,1,1,0,0,0,0,0,0]
theorem C34_7p0bound : C34_7p0.all wordBound = true := (by decide : [56,10,115,116,97,109,112,36,53,51,39,48,1,16,0,0,0,0,0,0,57,10,115,116,97,109,112,36,53,52,39,49,1,16,0,0,0,0,0,0,58,10,115,116,97,109,112,36,53,52,39,48,1,16,0,0,0,0,0,0,59,10,115,116,97,109,112,36,53,53,39,49,1,16,0,0,0,0,0,0,60,10,115,116,97,109,112,36,53,53,39,48,1,16,0,0,0,0,0,0,61,4,99,36,57,49,1,1,0,0,0,0,0,0,62,4,99,36,57,50,1,1,0,0,0,0,0,0].all wordBound = true)

def C34_7p1 : List Nat := [63,4,99,36,57,51,1,1,0,0,0,0,0,0]
theorem C34_7p1bound : C34_7p1.all wordBound = true := (by decide : [63,4,99,36,57,51,1,1,0,0,0,0,0,0].all wordBound = true)

def C34_7words : List Nat := C34_7p0 ++ C34_7p1

theorem C34_7wire : C34_7.flatMap columnWords = C34_7words := by
  rfl

theorem C34_7wordBound : C34_7words.all wordBound = true := by
  simp only [C34_7words,List.all_append,C34_7p0bound,C34_7p1bound]
  try rfl

theorem C34_7bounded : ∀ n ∈ C34_7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_7wordBound

theorem C34_7length : C34_7.length = 8 := by rfl

def C34_8 : List Column := [⟨64, [99,36,57,52], (some (1)), false, false, false⟩,⟨65, [99,36,57,53], (some (1)), false, false, false⟩,⟨66, [99,36,57,54], (some (1)), false, false, false⟩,⟨67, [99,36,57,55], (some (1)), false, false, false⟩,⟨68, [99,36,57,56], (some (1)), false, false, false⟩,⟨69, [99,36,49,48,55], (some (1)), false, false, false⟩,⟨70, [99,36,49,48,56], (some (1)), false, false, false⟩,⟨71, [99,36,49,48,57], (some (1)), false, false, false⟩]

def C34_8p0 : List Nat := [64,4,99,36,57,52,1,1,0,0,0,0,0,0,65,4,99,36,57,53,1,1,0,0,0,0,0,0,66,4,99,36,57,54,1,1,0,0,0,0,0,0,67,4,99,36,57,55,1,1,0,0,0,0,0,0,68,4,99,36,57,56,1,1,0,0,0,0,0,0,69,5,99,36,49,48,55,1,1,0,0,0,0,0,0,70,5,99,36,49,48,56,1,1,0,0,0,0,0,0,71,5,99,36,49,48,57,1,1,0,0,0,0,0,0]
theorem C34_8p0bound : C34_8p0.all wordBound = true := (by decide : [64,4,99,36,57,52,1,1,0,0,0,0,0,0,65,4,99,36,57,53,1,1,0,0,0,0,0,0,66,4,99,36,57,54,1,1,0,0,0,0,0,0,67,4,99,36,57,55,1,1,0,0,0,0,0,0,68,4,99,36,57,56,1,1,0,0,0,0,0,0,69,5,99,36,49,48,55,1,1,0,0,0,0,0,0,70,5,99,36,49,48,56,1,1,0,0,0,0,0,0,71,5,99,36,49,48,57,1,1,0,0,0,0,0,0].all wordBound = true)

def C34_8words : List Nat := C34_8p0

theorem C34_8wire : C34_8.flatMap columnWords = C34_8words := by
  rfl

theorem C34_8wordBound : C34_8words.all wordBound = true := by
  simp only [C34_8words,List.all_append,C34_8p0bound]
  try rfl

theorem C34_8bounded : ∀ n ∈ C34_8words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_8wordBound

theorem C34_8length : C34_8.length = 8 := by rfl

def C34_9 : List Column := [⟨72, [99,36,49,49,48], (some (1)), false, false, false⟩,⟨73, [102,108,97,36,55,51], (some (16)), false, false, false⟩,⟨74, [102,108,97,36,55,52], (some (16)), false, false, false⟩,⟨75, [102,108,97,36,55,53], (some (16)), false, false, false⟩,⟨76, [102,108,97,36,55,54], (some (16)), false, false, false⟩,⟨77, [36,114,101,116], (some (1)), false, false, false⟩,⟨78, [36,112,99], (some (2)), false, false, false⟩,⟨79, [36,105,115,95,112,99,95,49], (some (1)), false, false, false⟩]

def C34_9p0 : List Nat := [72,5,99,36,49,49,48,1,1,0,0,0,0,0,0,73,6,102,108,97,36,55,51,1,16,0,0,0,0,0,0,74,6,102,108,97,36,55,52,1,16,0,0,0,0,0,0,75,6,102,108,97,36,55,53,1,16,0,0,0,0,0,0,76,6,102,108,97,36,55,54,1,16,0,0,0,0,0,0,77,4,36,114,101,116,1,1,0,0,0,0,0,0,78,3,36,112,99,1,2,0,0,0,0,0,0,79,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0]
theorem C34_9p0bound : C34_9p0.all wordBound = true := (by decide : [72,5,99,36,49,49,48,1,1,0,0,0,0,0,0,73,6,102,108,97,36,55,51,1,16,0,0,0,0,0,0,74,6,102,108,97,36,55,52,1,16,0,0,0,0,0,0,75,6,102,108,97,36,55,53,1,16,0,0,0,0,0,0,76,6,102,108,97,36,55,54,1,16,0,0,0,0,0,0,77,4,36,114,101,116,1,1,0,0,0,0,0,0,78,3,36,112,99,1,2,0,0,0,0,0,0,79,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0].all wordBound = true)

def C34_9words : List Nat := C34_9p0

theorem C34_9wire : C34_9.flatMap columnWords = C34_9words := by
  rfl

theorem C34_9wordBound : C34_9words.all wordBound = true := by
  simp only [C34_9words,List.all_append,C34_9p0bound]
  try rfl

theorem C34_9bounded : ∀ n ∈ C34_9words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_9wordBound

theorem C34_9length : C34_9.length = 8 := by rfl

def C34_10 : List Column := [⟨80, [36,105,115,95,112,99,95,50], (some (1)), false, false, false⟩,⟨81, [36,105,115,95,112,99,95,51], (some (1)), false, false, false⟩,⟨82, [36,108,111,111,107,117,112,95,115,101,108,95,56,50], (some (1)), false, false, false⟩,⟨83, [36,108,111,111,107,117,112,95,115,101,108,95,56,51], (some (1)), false, false, false⟩,⟨84, [36,108,111,111,107,117,112,95,115,101,108,95,56,52], (some (1)), false, false, false⟩,⟨85, [40,105,110,118,32,109,97,116,95,109,117,108,95,101,120,116,101,114,110,97,108,58,36,112,99,41], none, false, false, true⟩,⟨86, [40,105,110,118,32,40,43,32,109,97,116,95,109,117,108,95,101,120,116,101,114,110,97,108,58,108,99,109,36,51,50,32,109,97,116,95,109,117,108,95,101,120,116,101,114,110,97,108,58,108,99,109,36,51,52,41,41], none, false, false, true⟩]

def C34_10p0 : List Nat := [80,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,81,8,36,105,115,95,112,99,95,51,1,1,0,0,0,0,0,0,82,14,36,108,111,111,107,117,112,95,115,101,108,95,56,50,1,1,0,0,0,0,0,0,83,14,36,108,111,111,107,117,112,95,115,101,108,95,56,51,1,1,0,0,0,0,0,0,84,14,36,108,111,111,107,117,112,95,115,101,108,95,56,52,1,1,0,0,0,0,0,0,85,26,40,105,110,118,32,109,97,116,95,109,117,108,95,101,120,116,101,114]
theorem C34_10p0bound : C34_10p0.all wordBound = true := (by decide : [80,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,81,8,36,105,115,95,112,99,95,51,1,1,0,0,0,0,0,0,82,14,36,108,111,111,107,117,112,95,115,101,108,95,56,50,1,1,0,0,0,0,0,0,83,14,36,108,111,111,107,117,112,95,115,101,108,95,56,51,1,1,0,0,0,0,0,0,84,14,36,108,111,111,107,117,112,95,115,101,108,95,56,52,1,1,0,0,0,0,0,0,85,26,40,105,110,118,32,109,97,116,95,109,117,108,95,101,120,116,101,114].all wordBound = true)

def C34_10p1 : List Nat := [110,97,108,58,36,112,99,41,0,0,0,0,0,0,1,0,86,57,40,105,110,118,32,40,43,32,109,97,116,95,109,117,108,95,101,120,116,101,114,110,97,108,58,108,99,109,36,51,50,32,109,97,116,95,109,117,108,95,101,120,116,101,114,110,97,108,58,108,99,109,36,51,52,41,41,0,0,0,0,0,0,1,0]
theorem C34_10p1bound : C34_10p1.all wordBound = true := (by decide : [110,97,108,58,36,112,99,41,0,0,0,0,0,0,1,0,86,57,40,105,110,118,32,40,43,32,109,97,116,95,109,117,108,95,101,120,116,101,114,110,97,108,58,108,99,109,36,51,50,32,109,97,116,95,109,117,108,95,101,120,116,101,114,110,97,108,58,108,99,109,36,51,52,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C34_10words : List Nat := C34_10p0 ++ C34_10p1

theorem C34_10wire : C34_10.flatMap columnWords = C34_10words := by
  rfl

theorem C34_10wordBound : C34_10words.all wordBound = true := by
  simp only [C34_10words,List.all_append,C34_10p0bound,C34_10p1bound]
  try rfl

theorem C34_10bounded : ∀ n ∈ C34_10words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C34_10wordBound

theorem C34_10length : C34_10.length = 7 := by rfl

def M34 : Module := ⟨34, [109,97,116,95,109,117,108,95,101,120,116,101,114,110,97,108], false, false, C34_0 ++ C34_1 ++ C34_2 ++ C34_3 ++ C34_4 ++ C34_5 ++ C34_6 ++ C34_7 ++ C34_8 ++ C34_9 ++ C34_10, ((List.range 0).map (fun n => [n]))⟩

def M34prefix : List Nat := [34,16,109,97,116,95,109,117,108,95,101,120,116,101,114,110,97,108,0,0,0,0,87]
theorem M34prefixwordBound : M34prefix.all wordBound = true := by decide

def M34words : List Nat := M34prefix ++ C34_0words ++ C34_1words ++ C34_2words ++ C34_3words ++ C34_4words ++ C34_5words ++ C34_6words ++ C34_7words ++ C34_8words ++ C34_9words ++ C34_10words ++ [0]

theorem M34wire : module.encode M34 = M34words := by
  rw [module_fast]
  simp only [M34,moduleWords,List.length_append,List.flatMap_append,C34_0length,C34_1length,C34_2length,C34_3length,C34_4length,C34_5length,C34_6length,C34_7length,C34_8length,C34_9length,C34_10length,C34_0wire,C34_1wire,C34_2wire,C34_3wire,C34_4wire,C34_5wire,C34_6wire,C34_7wire,C34_8wire,C34_9wire,C34_10wire]
  rfl

theorem M34wordBound : M34words.all wordBound = true := by
  simp only [M34words,List.all_append,M34prefixwordBound,C34_0wordBound,C34_1wordBound,C34_2wordBound,C34_3wordBound,C34_4wordBound,C34_5wordBound,C34_6wordBound,C34_7wordBound,C34_8wordBound,C34_9wordBound,C34_10wordBound]
  decide

theorem M34bounded : ∀ n ∈ M34words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M34wordBound

end DivRemFV.Replay
