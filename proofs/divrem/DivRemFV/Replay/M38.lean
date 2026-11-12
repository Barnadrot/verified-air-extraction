import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C38_0 : List Column := [⟨0, [114,101,103,105,115,116,101,114,115,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨1, [114,101,103,105,115,116,101,114,115,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨2, [114,101,103,105,115,116,101,114,115,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨3, [114,97,109,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨4, [114,97,109,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨5, [114,97,109,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨6, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨7, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩]

def C38_0p0 : List Nat := [0,17,114,101,103,105,115,116,101,114,115,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,17,114,101,103,105,115,116,101,114,115,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,17,114,101,103,105,115,116,101,114,115,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,4,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,5,11,114,97,109]
theorem C38_0p0bound : C38_0p0.all wordBound = true := (by decide : [0,17,114,101,103,105,115,116,101,114,115,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,17,114,101,103,105,115,116,101,114,115,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,17,114,101,103,105,115,116,101,114,115,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,4,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,5,11,114,97,109].all wordBound = true)

def C38_0p1 : List Nat := [36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,6,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,7,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0]
theorem C38_0p1bound : C38_0p1.all wordBound = true := (by decide : [36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,6,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,7,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0].all wordBound = true)

def C38_0words : List Nat := C38_0p0 ++ C38_0p1

theorem C38_0wire : C38_0.flatMap columnWords = C38_0words := by
  rfl

theorem C38_0wordBound : C38_0words.all wordBound = true := by
  simp only [C38_0words,List.all_append,C38_0p0bound,C38_0p1bound]
  try rfl

theorem C38_0bounded : ∀ n ∈ C38_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C38_0wordBound

theorem C38_0length : C38_0.length = 8 := by rfl

def C38_1 : List Column := [⟨8, [99,108,111,99,107,95,99,121,99,108,101,39,49], (some (16)), true, false, false⟩,⟨9, [99,108,111,99,107,95,99,121,99,108,101,39,48], (some (16)), true, false, false⟩,⟨10, [98,97,115,101,39,51], (some (16)), true, false, false⟩,⟨11, [98,97,115,101,39,50], (some (16)), true, false, false⟩,⟨12, [98,97,115,101,39,49], (some (16)), true, false, false⟩,⟨13, [98,97,115,101,39,48], (some (16)), true, false, false⟩,⟨14, [112,99,39,51], (some (16)), true, false, false⟩,⟨15, [112,99,39,50], (some (16)), true, false, false⟩]

def C38_1p0 : List Nat := [8,13,99,108,111,99,107,95,99,121,99,108,101,39,49,1,16,1,0,0,0,0,0,9,13,99,108,111,99,107,95,99,121,99,108,101,39,48,1,16,1,0,0,0,0,0,10,6,98,97,115,101,39,51,1,16,1,0,0,0,0,0,11,6,98,97,115,101,39,50,1,16,1,0,0,0,0,0,12,6,98,97,115,101,39,49,1,16,1,0,0,0,0,0,13,6,98,97,115,101,39,48,1,16,1,0,0,0,0,0,14,4,112,99,39,51,1,16,1,0,0,0,0,0,15,4,112,99]
theorem C38_1p0bound : C38_1p0.all wordBound = true := (by decide : [8,13,99,108,111,99,107,95,99,121,99,108,101,39,49,1,16,1,0,0,0,0,0,9,13,99,108,111,99,107,95,99,121,99,108,101,39,48,1,16,1,0,0,0,0,0,10,6,98,97,115,101,39,51,1,16,1,0,0,0,0,0,11,6,98,97,115,101,39,50,1,16,1,0,0,0,0,0,12,6,98,97,115,101,39,49,1,16,1,0,0,0,0,0,13,6,98,97,115,101,39,48,1,16,1,0,0,0,0,0,14,4,112,99,39,51,1,16,1,0,0,0,0,0,15,4,112,99].all wordBound = true)

def C38_1p1 : List Nat := [39,50,1,16,1,0,0,0,0,0]
theorem C38_1p1bound : C38_1p1.all wordBound = true := (by decide : [39,50,1,16,1,0,0,0,0,0].all wordBound = true)

def C38_1words : List Nat := C38_1p0 ++ C38_1p1

theorem C38_1wire : C38_1.flatMap columnWords = C38_1words := by
  rfl

theorem C38_1wordBound : C38_1words.all wordBound = true := by
  simp only [C38_1words,List.all_append,C38_1p0bound,C38_1p1bound]
  try rfl

theorem C38_1bounded : ∀ n ∈ C38_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C38_1wordBound

theorem C38_1length : C38_1.length = 8 := by rfl

def C38_2 : List Column := [⟨16, [112,99,39,49], (some (16)), true, false, false⟩,⟨17, [112,99,39,48], (some (16)), true, false, false⟩,⟨18, [110,101,119,95,112,99,39,51], (some (16)), false, false, false⟩,⟨19, [110,101,119,95,112,99,39,50], (some (16)), false, false, false⟩,⟨20, [110,101,119,95,112,99,39,49], (some (16)), false, false, false⟩,⟨21, [110,101,119,95,112,99,39,48], (some (16)), false, false, false⟩,⟨22, [105,110,100,101,120,39,51], (some (14)), false, false, false⟩,⟨23, [105,110,100,101,120,39,50], (some (16)), false, false, false⟩]

def C38_2p0 : List Nat := [16,4,112,99,39,49,1,16,1,0,0,0,0,0,17,4,112,99,39,48,1,16,1,0,0,0,0,0,18,8,110,101,119,95,112,99,39,51,1,16,0,0,0,0,0,0,19,8,110,101,119,95,112,99,39,50,1,16,0,0,0,0,0,0,20,8,110,101,119,95,112,99,39,49,1,16,0,0,0,0,0,0,21,8,110,101,119,95,112,99,39,48,1,16,0,0,0,0,0,0,22,7,105,110,100,101,120,39,51,1,14,0,0,0,0,0,0,23,7,105,110,100,101,120,39,50,1,16]
theorem C38_2p0bound : C38_2p0.all wordBound = true := (by decide : [16,4,112,99,39,49,1,16,1,0,0,0,0,0,17,4,112,99,39,48,1,16,1,0,0,0,0,0,18,8,110,101,119,95,112,99,39,51,1,16,0,0,0,0,0,0,19,8,110,101,119,95,112,99,39,50,1,16,0,0,0,0,0,0,20,8,110,101,119,95,112,99,39,49,1,16,0,0,0,0,0,0,21,8,110,101,119,95,112,99,39,48,1,16,0,0,0,0,0,0,22,7,105,110,100,101,120,39,51,1,14,0,0,0,0,0,0,23,7,105,110,100,101,120,39,50,1,16].all wordBound = true)

def C38_2p1 : List Nat := [0,0,0,0,0,0]
theorem C38_2p1bound : C38_2p1.all wordBound = true := (by decide : [0,0,0,0,0,0].all wordBound = true)

def C38_2words : List Nat := C38_2p0 ++ C38_2p1

theorem C38_2wire : C38_2.flatMap columnWords = C38_2words := by
  rfl

theorem C38_2wordBound : C38_2words.all wordBound = true := by
  simp only [C38_2words,List.all_append,C38_2p0bound,C38_2p1bound]
  try rfl

theorem C38_2bounded : ∀ n ∈ C38_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C38_2wordBound

theorem C38_2length : C38_2.length = 8 := by rfl

def C38_3 : List Column := [⟨24, [105,110,100,101,120,39,49], (some (16)), false, false, false⟩,⟨25, [105,110,100,101,120,39,48], (some (16)), false, false, false⟩,⟨26, [114,101,109], (some (2)), false, false, false⟩,⟨27, [36,54,39,49], (some (16)), false, false, false⟩,⟨28, [36,54,39,48], (some (16)), false, false, false⟩,⟨29, [115,116,97,109,112,36,49,48,39,50], (some (16)), false, false, false⟩,⟨30, [115,116,97,109,112,36,49,48,39,49], (some (16)), false, false, false⟩,⟨31, [115,116,97,109,112,36,49,48,39,48], (some (16)), false, false, false⟩]

def C38_3p0 : List Nat := [24,7,105,110,100,101,120,39,49,1,16,0,0,0,0,0,0,25,7,105,110,100,101,120,39,48,1,16,0,0,0,0,0,0,26,3,114,101,109,1,2,0,0,0,0,0,0,27,4,36,54,39,49,1,16,0,0,0,0,0,0,28,4,36,54,39,48,1,16,0,0,0,0,0,0,29,10,115,116,97,109,112,36,49,48,39,50,1,16,0,0,0,0,0,0,30,10,115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0,31,10,115,116,97,109,112,36,49,48,39,48,1]
theorem C38_3p0bound : C38_3p0.all wordBound = true := (by decide : [24,7,105,110,100,101,120,39,49,1,16,0,0,0,0,0,0,25,7,105,110,100,101,120,39,48,1,16,0,0,0,0,0,0,26,3,114,101,109,1,2,0,0,0,0,0,0,27,4,36,54,39,49,1,16,0,0,0,0,0,0,28,4,36,54,39,48,1,16,0,0,0,0,0,0,29,10,115,116,97,109,112,36,49,48,39,50,1,16,0,0,0,0,0,0,30,10,115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0,31,10,115,116,97,109,112,36,49,48,39,48,1].all wordBound = true)

def C38_3p1 : List Nat := [16,0,0,0,0,0,0]
theorem C38_3p1bound : C38_3p1.all wordBound = true := (by decide : [16,0,0,0,0,0,0].all wordBound = true)

def C38_3words : List Nat := C38_3p0 ++ C38_3p1

theorem C38_3wire : C38_3.flatMap columnWords = C38_3words := by
  rfl

theorem C38_3wordBound : C38_3words.all wordBound = true := by
  simp only [C38_3words,List.all_append,C38_3p0bound,C38_3p1bound]
  try rfl

theorem C38_3bounded : ∀ n ∈ C38_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C38_3wordBound

theorem C38_3length : C38_3.length = 8 := by rfl

def C38_4 : List Column := [⟨32, [115,116,97,109,112,36,49,49,39,50], (some (16)), false, false, false⟩,⟨33, [115,116,97,109,112,36,49,49,39,49], (some (16)), false, false, false⟩,⟨34, [115,116,97,109,112,36,49,49,39,48], (some (16)), false, false, false⟩,⟨35, [115,116,97,109,112,36,49,50,39,49], (some (16)), false, false, false⟩,⟨36, [115,116,97,109,112,36,49,50,39,48], (some (16)), false, false, false⟩,⟨37, [102,115,99,36,49,51], (some (1)), false, false, false⟩,⟨38, [116,36,51,56], (some (14)), false, false, false⟩,⟨39, [116,36,51,57], (some (2)), false, false, false⟩]

def C38_4p0 : List Nat := [32,10,115,116,97,109,112,36,49,49,39,50,1,16,0,0,0,0,0,0,33,10,115,116,97,109,112,36,49,49,39,49,1,16,0,0,0,0,0,0,34,10,115,116,97,109,112,36,49,49,39,48,1,16,0,0,0,0,0,0,35,10,115,116,97,109,112,36,49,50,39,49,1,16,0,0,0,0,0,0,36,10,115,116,97,109,112,36,49,50,39,48,1,16,0,0,0,0,0,0,37,6,102,115,99,36,49,51,1,1,0,0,0,0,0,0,38,4,116,36,51,56,1,14,0,0,0,0]
theorem C38_4p0bound : C38_4p0.all wordBound = true := (by decide : [32,10,115,116,97,109,112,36,49,49,39,50,1,16,0,0,0,0,0,0,33,10,115,116,97,109,112,36,49,49,39,49,1,16,0,0,0,0,0,0,34,10,115,116,97,109,112,36,49,49,39,48,1,16,0,0,0,0,0,0,35,10,115,116,97,109,112,36,49,50,39,49,1,16,0,0,0,0,0,0,36,10,115,116,97,109,112,36,49,50,39,48,1,16,0,0,0,0,0,0,37,6,102,115,99,36,49,51,1,1,0,0,0,0,0,0,38,4,116,36,51,56,1,14,0,0,0,0].all wordBound = true)

def C38_4p1 : List Nat := [0,0,39,4,116,36,51,57,1,2,0,0,0,0,0,0]
theorem C38_4p1bound : C38_4p1.all wordBound = true := (by decide : [0,0,39,4,116,36,51,57,1,2,0,0,0,0,0,0].all wordBound = true)

def C38_4words : List Nat := C38_4p0 ++ C38_4p1

theorem C38_4wire : C38_4.flatMap columnWords = C38_4words := by
  rfl

theorem C38_4wordBound : C38_4words.all wordBound = true := by
  simp only [C38_4words,List.all_append,C38_4p0bound,C38_4p1bound]
  try rfl

theorem C38_4bounded : ∀ n ∈ C38_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C38_4wordBound

theorem C38_4length : C38_4.length = 8 := by rfl

def C38_5 : List Column := [⟨40, [116,36,52,48], (some (14)), false, false, false⟩,⟨41, [116,36,52,49], (some (2)), false, false, false⟩,⟨42, [116,36,52,50], (some (14)), false, false, false⟩,⟨43, [116,36,52,51], (some (2)), false, false, false⟩,⟨44, [98,36,52,52], (some (1)), false, false, false⟩,⟨45, [98,36,52,53], (some (1)), false, false, false⟩,⟨46, [98,36,52,54], (some (1)), false, false, false⟩,⟨47, [99,36,52,55], (some (1)), false, false, false⟩]

def C38_5p0 : List Nat := [40,4,116,36,52,48,1,14,0,0,0,0,0,0,41,4,116,36,52,49,1,2,0,0,0,0,0,0,42,4,116,36,52,50,1,14,0,0,0,0,0,0,43,4,116,36,52,51,1,2,0,0,0,0,0,0,44,4,98,36,52,52,1,1,0,0,0,0,0,0,45,4,98,36,52,53,1,1,0,0,0,0,0,0,46,4,98,36,52,54,1,1,0,0,0,0,0,0,47,4,99,36,52,55,1,1,0,0,0,0,0,0]
theorem C38_5p0bound : C38_5p0.all wordBound = true := (by decide : [40,4,116,36,52,48,1,14,0,0,0,0,0,0,41,4,116,36,52,49,1,2,0,0,0,0,0,0,42,4,116,36,52,50,1,14,0,0,0,0,0,0,43,4,116,36,52,51,1,2,0,0,0,0,0,0,44,4,98,36,52,52,1,1,0,0,0,0,0,0,45,4,98,36,52,53,1,1,0,0,0,0,0,0,46,4,98,36,52,54,1,1,0,0,0,0,0,0,47,4,99,36,52,55,1,1,0,0,0,0,0,0].all wordBound = true)

def C38_5words : List Nat := C38_5p0

theorem C38_5wire : C38_5.flatMap columnWords = C38_5words := by
  rfl

theorem C38_5wordBound : C38_5words.all wordBound = true := by
  simp only [C38_5words,List.all_append,C38_5p0bound]
  try rfl

theorem C38_5bounded : ∀ n ∈ C38_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C38_5wordBound

theorem C38_5length : C38_5.length = 8 := by rfl

def C38_6 : List Column := [⟨48, [36,114,101,116], (some (1)), false, false, false⟩,⟨49, [36,108,111,111,107,117,112,95,115,101,108,95,52,57], (some (1)), false, false, false⟩,⟨50, [40,105,110,118,32,40,43,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,51,41,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,50,41,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,49,41,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,48,41,41,41], none, false, false, true⟩]

def C38_6p0 : List Nat := [48,4,36,114,101,116,1,1,0,0,0,0,0,0,49,14,36,108,111,111,107,117,112,95,115,101,108,95,52,57,1,1,0,0,0,0,0,0,50,133,40,105,110,118,32,40,43,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,51,41,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,50,41,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116]
theorem C38_6p0bound : C38_6p0.all wordBound = true := (by decide : [48,4,36,114,101,116,1,1,0,0,0,0,0,0,49,14,36,108,111,111,107,117,112,95,115,101,108,95,52,57,1,1,0,0,0,0,0,0,50,133,40,105,110,118,32,40,43,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,51,41,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,50,41,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116].all wordBound = true)

def C38_6p1 : List Nat := [101,114,58,110,101,119,95,112,99,39,49,41,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,48,41,41,41,0,0,0,0,0,0,1,0]
theorem C38_6p1bound : C38_6p1.all wordBound = true := (by decide : [101,114,58,110,101,119,95,112,99,39,49,41,32,40,45,32,54,53,53,51,53,32,105,110,116,101,114,112,114,101,116,101,114,58,110,101,119,95,112,99,39,48,41,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C38_6words : List Nat := C38_6p0 ++ C38_6p1

theorem C38_6wire : C38_6.flatMap columnWords = C38_6words := by
  rfl

theorem C38_6wordBound : C38_6words.all wordBound = true := by
  simp only [C38_6words,List.all_append,C38_6p0bound,C38_6p1bound]
  try rfl

theorem C38_6bounded : ∀ n ∈ C38_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C38_6wordBound

theorem C38_6length : C38_6.length = 3 := by rfl

def M38 : Module := ⟨38, [105,110,116,101,114,112,114,101,116,101,114], false, false, C38_0 ++ C38_1 ++ C38_2 ++ C38_3 ++ C38_4 ++ C38_5 ++ C38_6, ((List.range 0).map (fun n => [n]))⟩

def M38prefix : List Nat := [38,11,105,110,116,101,114,112,114,101,116,101,114,0,0,0,0,51]
theorem M38prefixwordBound : M38prefix.all wordBound = true := by decide

def M38words : List Nat := M38prefix ++ C38_0words ++ C38_1words ++ C38_2words ++ C38_3words ++ C38_4words ++ C38_5words ++ C38_6words ++ [0]

theorem M38wire : module.encode M38 = M38words := by
  rw [module_fast]
  simp only [M38,moduleWords,List.length_append,List.flatMap_append,C38_0length,C38_1length,C38_2length,C38_3length,C38_4length,C38_5length,C38_6length,C38_0wire,C38_1wire,C38_2wire,C38_3wire,C38_4wire,C38_5wire,C38_6wire]
  rfl

theorem M38wordBound : M38words.all wordBound = true := by
  simp only [M38words,List.all_append,M38prefixwordBound,C38_0wordBound,C38_1wordBound,C38_2wordBound,C38_3wordBound,C38_4wordBound,C38_5wordBound,C38_6wordBound]
  decide

theorem M38bounded : ∀ n ∈ M38words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M38wordBound

end DivRemFV.Replay
