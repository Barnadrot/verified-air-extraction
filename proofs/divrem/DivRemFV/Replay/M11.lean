import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C11_0 : List Column := [⟨0, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨3, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨4, [105], (some (7)), false, false, false⟩,⟨5, [36,49], (some (7)), false, false, false⟩,⟨6, [36,50,39,51], (some (16)), false, false, false⟩,⟨7, [36,50,39,50], (some (16)), false, false, false⟩]

def C11_0p0 : List Nat := [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0]
theorem C11_0p0bound : C11_0p0.all wordBound = true := (by decide : [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C11_0p1 : List Nat := [4,1,105,1,7,0,0,0,0,0,0,5,2,36,49,1,7,0,0,0,0,0,0,6,4,36,50,39,51,1,16,0,0,0,0,0,0,7,4,36,50,39,50,1,16,0,0,0,0,0,0]
theorem C11_0p1bound : C11_0p1.all wordBound = true := (by decide : [4,1,105,1,7,0,0,0,0,0,0,5,2,36,49,1,7,0,0,0,0,0,0,6,4,36,50,39,51,1,16,0,0,0,0,0,0,7,4,36,50,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C11_0words : List Nat := C11_0p0 ++ C11_0p1

theorem C11_0wire : C11_0.flatMap columnWords = C11_0words := by
  rfl

theorem C11_0wordBound : C11_0words.all wordBound = true := by
  simp only [C11_0words,List.all_append,C11_0p0bound,C11_0p1bound]
  try rfl

theorem C11_0bounded : ∀ n ∈ C11_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C11_0wordBound

theorem C11_0length : C11_0.length = 8 := by rfl

def C11_1 : List Column := [⟨8, [36,50,39,49], (some (16)), false, false, false⟩,⟨9, [36,50,39,48], (some (16)), false, false, false⟩,⟨10, [36,51], (some (7)), false, false, false⟩,⟨11, [36,52,39,51], (some (16)), false, false, false⟩,⟨12, [36,52,39,50], (some (16)), false, false, false⟩,⟨13, [36,52,39,49], (some (16)), false, false, false⟩,⟨14, [36,52,39,48], (some (16)), false, false, false⟩,⟨15, [36,53], (some (7)), false, false, false⟩]

def C11_1p0 : List Nat := [8,4,36,50,39,49,1,16,0,0,0,0,0,0,9,4,36,50,39,48,1,16,0,0,0,0,0,0,10,2,36,51,1,7,0,0,0,0,0,0,11,4,36,52,39,51,1,16,0,0,0,0,0,0,12,4,36,52,39,50,1,16,0,0,0,0,0,0,13,4,36,52,39,49,1,16,0,0,0,0,0,0,14,4,36,52,39,48,1,16,0,0,0,0,0,0,15,2,36,53,1,7,0,0,0,0,0,0]
theorem C11_1p0bound : C11_1p0.all wordBound = true := (by decide : [8,4,36,50,39,49,1,16,0,0,0,0,0,0,9,4,36,50,39,48,1,16,0,0,0,0,0,0,10,2,36,51,1,7,0,0,0,0,0,0,11,4,36,52,39,51,1,16,0,0,0,0,0,0,12,4,36,52,39,50,1,16,0,0,0,0,0,0,13,4,36,52,39,49,1,16,0,0,0,0,0,0,14,4,36,52,39,48,1,16,0,0,0,0,0,0,15,2,36,53,1,7,0,0,0,0,0,0].all wordBound = true)

def C11_1words : List Nat := C11_1p0

theorem C11_1wire : C11_1.flatMap columnWords = C11_1words := by
  rfl

theorem C11_1wordBound : C11_1words.all wordBound = true := by
  simp only [C11_1words,List.all_append,C11_1p0bound]
  try rfl

theorem C11_1bounded : ∀ n ∈ C11_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C11_1wordBound

theorem C11_1length : C11_1.length = 8 := by rfl

def C11_2 : List Column := [⟨16, [36,54,39,51], (some (16)), false, false, false⟩,⟨17, [36,54,39,50], (some (16)), false, false, false⟩,⟨18, [36,54,39,49], (some (16)), false, false, false⟩,⟨19, [36,54,39,48], (some (16)), false, false, false⟩,⟨20, [36,55], (some (7)), false, false, false⟩,⟨21, [36,56,39,51], (some (16)), false, false, false⟩,⟨22, [36,56,39,50], (some (16)), false, false, false⟩,⟨23, [36,56,39,49], (some (16)), false, false, false⟩]

def C11_2p0 : List Nat := [16,4,36,54,39,51,1,16,0,0,0,0,0,0,17,4,36,54,39,50,1,16,0,0,0,0,0,0,18,4,36,54,39,49,1,16,0,0,0,0,0,0,19,4,36,54,39,48,1,16,0,0,0,0,0,0,20,2,36,55,1,7,0,0,0,0,0,0,21,4,36,56,39,51,1,16,0,0,0,0,0,0,22,4,36,56,39,50,1,16,0,0,0,0,0,0,23,4,36,56,39,49,1,16,0,0,0,0,0,0]
theorem C11_2p0bound : C11_2p0.all wordBound = true := (by decide : [16,4,36,54,39,51,1,16,0,0,0,0,0,0,17,4,36,54,39,50,1,16,0,0,0,0,0,0,18,4,36,54,39,49,1,16,0,0,0,0,0,0,19,4,36,54,39,48,1,16,0,0,0,0,0,0,20,2,36,55,1,7,0,0,0,0,0,0,21,4,36,56,39,51,1,16,0,0,0,0,0,0,22,4,36,56,39,50,1,16,0,0,0,0,0,0,23,4,36,56,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C11_2words : List Nat := C11_2p0

theorem C11_2wire : C11_2.flatMap columnWords = C11_2words := by
  rfl

theorem C11_2wordBound : C11_2words.all wordBound = true := by
  simp only [C11_2words,List.all_append,C11_2p0bound]
  try rfl

theorem C11_2bounded : ∀ n ∈ C11_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C11_2wordBound

theorem C11_2length : C11_2.length = 8 := by rfl

def C11_3 : List Column := [⟨24, [36,56,39,48], (some (16)), false, false, false⟩,⟨25, [36,57], (some (7)), false, false, false⟩,⟨26, [36,49,48,39,51], (some (16)), false, false, false⟩,⟨27, [36,49,48,39,50], (some (16)), false, false, false⟩,⟨28, [36,49,48,39,49], (some (16)), false, false, false⟩,⟨29, [36,49,48,39,48], (some (16)), false, false, false⟩,⟨30, [108,99,109,36,49,49], (some (7)), false, false, false⟩,⟨31, [108,99,109,36,49,50], (some (1)), false, false, false⟩]

def C11_3p0 : List Nat := [24,4,36,56,39,48,1,16,0,0,0,0,0,0,25,2,36,57,1,7,0,0,0,0,0,0,26,5,36,49,48,39,51,1,16,0,0,0,0,0,0,27,5,36,49,48,39,50,1,16,0,0,0,0,0,0,28,5,36,49,48,39,49,1,16,0,0,0,0,0,0,29,5,36,49,48,39,48,1,16,0,0,0,0,0,0,30,6,108,99,109,36,49,49,1,7,0,0,0,0,0,0,31,6,108,99,109,36,49,50,1,1,0,0,0,0,0,0]
theorem C11_3p0bound : C11_3p0.all wordBound = true := (by decide : [24,4,36,56,39,48,1,16,0,0,0,0,0,0,25,2,36,57,1,7,0,0,0,0,0,0,26,5,36,49,48,39,51,1,16,0,0,0,0,0,0,27,5,36,49,48,39,50,1,16,0,0,0,0,0,0,28,5,36,49,48,39,49,1,16,0,0,0,0,0,0,29,5,36,49,48,39,48,1,16,0,0,0,0,0,0,30,6,108,99,109,36,49,49,1,7,0,0,0,0,0,0,31,6,108,99,109,36,49,50,1,1,0,0,0,0,0,0].all wordBound = true)

def C11_3words : List Nat := C11_3p0

theorem C11_3wire : C11_3.flatMap columnWords = C11_3words := by
  rfl

theorem C11_3wordBound : C11_3words.all wordBound = true := by
  simp only [C11_3words,List.all_append,C11_3p0bound]
  try rfl

theorem C11_3bounded : ∀ n ∈ C11_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C11_3wordBound

theorem C11_3length : C11_3.length = 8 := by rfl

def C11_4 : List Column := [⟨32, [115,116,97,109,112,36,49,53,39,49], (some (16)), false, false, false⟩,⟨33, [115,116,97,109,112,36,49,53,39,48], (some (16)), false, false, false⟩,⟨34, [115,116,97,109,112,36,49,54,39,49], (some (16)), false, false, false⟩,⟨35, [115,116,97,109,112,36,49,54,39,48], (some (16)), false, false, false⟩,⟨36, [115,116,97,109,112,36,49,55,39,49], (some (16)), false, false, false⟩,⟨37, [115,116,97,109,112,36,49,55,39,48], (some (16)), false, false, false⟩,⟨38, [115,116,97,109,112,36,49,56,39,49], (some (16)), false, false, false⟩,⟨39, [115,116,97,109,112,36,49,56,39,48], (some (16)), false, false, false⟩]

def C11_4p0 : List Nat := [32,10,115,116,97,109,112,36,49,53,39,49,1,16,0,0,0,0,0,0,33,10,115,116,97,109,112,36,49,53,39,48,1,16,0,0,0,0,0,0,34,10,115,116,97,109,112,36,49,54,39,49,1,16,0,0,0,0,0,0,35,10,115,116,97,109,112,36,49,54,39,48,1,16,0,0,0,0,0,0,36,10,115,116,97,109,112,36,49,55,39,49,1,16,0,0,0,0,0,0,37,10,115,116,97,109,112,36,49,55,39,48,1,16,0,0,0,0,0,0,38,10,115,116,97,109,112,36]
theorem C11_4p0bound : C11_4p0.all wordBound = true := (by decide : [32,10,115,116,97,109,112,36,49,53,39,49,1,16,0,0,0,0,0,0,33,10,115,116,97,109,112,36,49,53,39,48,1,16,0,0,0,0,0,0,34,10,115,116,97,109,112,36,49,54,39,49,1,16,0,0,0,0,0,0,35,10,115,116,97,109,112,36,49,54,39,48,1,16,0,0,0,0,0,0,36,10,115,116,97,109,112,36,49,55,39,49,1,16,0,0,0,0,0,0,37,10,115,116,97,109,112,36,49,55,39,48,1,16,0,0,0,0,0,0,38,10,115,116,97,109,112,36].all wordBound = true)

def C11_4p1 : List Nat := [49,56,39,49,1,16,0,0,0,0,0,0,39,10,115,116,97,109,112,36,49,56,39,48,1,16,0,0,0,0,0,0]
theorem C11_4p1bound : C11_4p1.all wordBound = true := (by decide : [49,56,39,49,1,16,0,0,0,0,0,0,39,10,115,116,97,109,112,36,49,56,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C11_4words : List Nat := C11_4p0 ++ C11_4p1

theorem C11_4wire : C11_4.flatMap columnWords = C11_4words := by
  rfl

theorem C11_4wordBound : C11_4words.all wordBound = true := by
  simp only [C11_4words,List.all_append,C11_4p0bound,C11_4p1bound]
  try rfl

theorem C11_4bounded : ∀ n ∈ C11_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C11_4wordBound

theorem C11_4length : C11_4.length = 8 := by rfl

def C11_5 : List Column := [⟨40, [99,36,52,56], (some (1)), false, false, false⟩,⟨41, [99,36,52,57], (some (1)), false, false, false⟩,⟨42, [99,36,53,48], (some (1)), false, false, false⟩,⟨43, [99,36,53,49], (some (1)), false, false, false⟩,⟨44, [99,36,53,50], (some (1)), false, false, false⟩,⟨45, [102,108,97,36,52,53], (some (16)), false, false, false⟩,⟨46, [102,108,97,36,52,54], (some (16)), false, false, false⟩,⟨47, [36,114,101,116], (some (1)), false, false, false⟩]

def C11_5p0 : List Nat := [40,4,99,36,52,56,1,1,0,0,0,0,0,0,41,4,99,36,52,57,1,1,0,0,0,0,0,0,42,4,99,36,53,48,1,1,0,0,0,0,0,0,43,4,99,36,53,49,1,1,0,0,0,0,0,0,44,4,99,36,53,50,1,1,0,0,0,0,0,0,45,6,102,108,97,36,52,53,1,16,0,0,0,0,0,0,46,6,102,108,97,36,52,54,1,16,0,0,0,0,0,0,47,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C11_5p0bound : C11_5p0.all wordBound = true := (by decide : [40,4,99,36,52,56,1,1,0,0,0,0,0,0,41,4,99,36,52,57,1,1,0,0,0,0,0,0,42,4,99,36,53,48,1,1,0,0,0,0,0,0,43,4,99,36,53,49,1,1,0,0,0,0,0,0,44,4,99,36,53,50,1,1,0,0,0,0,0,0,45,6,102,108,97,36,52,53,1,16,0,0,0,0,0,0,46,6,102,108,97,36,52,54,1,16,0,0,0,0,0,0,47,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C11_5words : List Nat := C11_5p0

theorem C11_5wire : C11_5.flatMap columnWords = C11_5words := by
  rfl

theorem C11_5wordBound : C11_5words.all wordBound = true := by
  simp only [C11_5words,List.all_append,C11_5p0bound]
  try rfl

theorem C11_5bounded : ∀ n ∈ C11_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C11_5wordBound

theorem C11_5length : C11_5.length = 8 := by rfl

def C11_6 : List Column := [⟨48, [36,112,99], (some (2)), false, false, false⟩,⟨49, [36,105,115,95,112,99,95,49], (some (1)), false, false, false⟩,⟨50, [36,105,115,95,112,99,95,50], (some (1)), false, false, false⟩,⟨51, [36,108,111,111,107,117,112,95,115,101,108,95,53,49], (some (1)), false, false, false⟩,⟨52, [36,108,111,111,107,117,112,95,115,101,108,95,53,50], (some (1)), false, false, false⟩,⟨53, [40,105,110,118,32,119,105,112,101,95,115,116,97,116,101,58,36,112,99,41], none, false, false, true⟩]

def C11_6p0 : List Nat := [48,3,36,112,99,1,2,0,0,0,0,0,0,49,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,50,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,51,14,36,108,111,111,107,117,112,95,115,101,108,95,53,49,1,1,0,0,0,0,0,0,52,14,36,108,111,111,107,117,112,95,115,101,108,95,53,50,1,1,0,0,0,0,0,0,53,20,40,105,110,118,32,119,105,112,101,95,115,116,97,116,101,58,36,112,99,41,0,0,0,0,0,0,1,0]
theorem C11_6p0bound : C11_6p0.all wordBound = true := (by decide : [48,3,36,112,99,1,2,0,0,0,0,0,0,49,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,50,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,51,14,36,108,111,111,107,117,112,95,115,101,108,95,53,49,1,1,0,0,0,0,0,0,52,14,36,108,111,111,107,117,112,95,115,101,108,95,53,50,1,1,0,0,0,0,0,0,53,20,40,105,110,118,32,119,105,112,101,95,115,116,97,116,101,58,36,112,99,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C11_6words : List Nat := C11_6p0

theorem C11_6wire : C11_6.flatMap columnWords = C11_6words := by
  rfl

theorem C11_6wordBound : C11_6words.all wordBound = true := by
  simp only [C11_6words,List.all_append,C11_6p0bound]
  try rfl

theorem C11_6bounded : ∀ n ∈ C11_6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C11_6wordBound

theorem C11_6length : C11_6.length = 6 := by rfl

def M11 : Module := ⟨11, [119,105,112,101,95,115,116,97,116,101], false, false, C11_0 ++ C11_1 ++ C11_2 ++ C11_3 ++ C11_4 ++ C11_5 ++ C11_6, ((List.range 0).map (fun n => [n]))⟩

def M11prefix : List Nat := [11,10,119,105,112,101,95,115,116,97,116,101,0,0,0,0,54]
theorem M11prefixwordBound : M11prefix.all wordBound = true := by decide

def M11words : List Nat := M11prefix ++ C11_0words ++ C11_1words ++ C11_2words ++ C11_3words ++ C11_4words ++ C11_5words ++ C11_6words ++ [0]

theorem M11wire : module.encode M11 = M11words := by
  rw [module_fast]
  simp only [M11,moduleWords,List.length_append,List.flatMap_append,C11_0length,C11_1length,C11_2length,C11_3length,C11_4length,C11_5length,C11_6length,C11_0wire,C11_1wire,C11_2wire,C11_3wire,C11_4wire,C11_5wire,C11_6wire]
  rfl

theorem M11wordBound : M11words.all wordBound = true := by
  simp only [M11words,List.all_append,M11prefixwordBound,C11_0wordBound,C11_1wordBound,C11_2wordBound,C11_3wordBound,C11_4wordBound,C11_5wordBound,C11_6wordBound]
  decide

theorem M11bounded : ∀ n ∈ M11words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M11wordBound

end DivRemFV.Replay
