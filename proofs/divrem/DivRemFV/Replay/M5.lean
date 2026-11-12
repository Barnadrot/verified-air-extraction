import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C5_0 : List Column := [⟨0, [114,97,109,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨1, [114,97,109,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨2, [114,97,109,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨3, [111,102,102,115,101,116,39,51], (some (16)), true, false, false⟩,⟨4, [111,102,102,115,101,116,39,50], (some (16)), true, false, false⟩,⟨5, [111,102,102,115,101,116,39,49], (some (16)), true, false, false⟩,⟨6, [111,102,102,115,101,116,39,48], (some (16)), true, false, false⟩,⟨7, [115,105,122,101,39,49], (some (16)), true, false, false⟩]

def C5_0p0 : List Nat := [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,8,111,102,102,115,101,116,39,51,1,16,1,0,0,0,0,0,4,8,111,102,102,115,101,116,39,50,1,16,1,0,0,0,0,0,5,8,111,102,102,115,101,116,39,49,1,16,1,0,0,0,0,0,6,8,111,102,102,115,101,116,39,48,1]
theorem C5_0p0bound : C5_0p0.all wordBound = true := (by decide : [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,8,111,102,102,115,101,116,39,51,1,16,1,0,0,0,0,0,4,8,111,102,102,115,101,116,39,50,1,16,1,0,0,0,0,0,5,8,111,102,102,115,101,116,39,49,1,16,1,0,0,0,0,0,6,8,111,102,102,115,101,116,39,48,1].all wordBound = true)

def C5_0p1 : List Nat := [16,1,0,0,0,0,0,7,6,115,105,122,101,39,49,1,16,1,0,0,0,0,0]
theorem C5_0p1bound : C5_0p1.all wordBound = true := (by decide : [16,1,0,0,0,0,0,7,6,115,105,122,101,39,49,1,16,1,0,0,0,0,0].all wordBound = true)

def C5_0words : List Nat := C5_0p0 ++ C5_0p1

theorem C5_0wire : C5_0.flatMap columnWords = C5_0words := by
  rfl

theorem C5_0wordBound : C5_0words.all wordBound = true := by
  simp only [C5_0words,List.all_append,C5_0p0bound,C5_0p1bound]
  try rfl

theorem C5_0bounded : ∀ n ∈ C5_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C5_0wordBound

theorem C5_0length : C5_0.length = 8 := by rfl

def C5_1 : List Column := [⟨8, [115,105,122,101,39,48], (some (16)), true, false, false⟩,⟨9, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,50], (some (16)), false, true, false⟩,⟨10, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨11, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨12, [105,39,49], (some (16)), false, false, false⟩,⟨13, [105,39,48], (some (16)), false, false, false⟩,⟨14, [98,121,116,101,95,114,101,97,100], (some (8)), false, false, false⟩,⟨15, [36,52,39,51], (some (16)), false, false, false⟩]

def C5_1p0 : List Nat := [8,6,115,105,122,101,39,48,1,16,1,0,0,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,10,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,11,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,12,3,105,39,49,1,16,0,0,0,0,0,0,13,3,105,39,48,1,16,0,0,0,0,0,0,14,9,98,121,116,101,95,114,101,97,100]
theorem C5_1p0bound : C5_1p0.all wordBound = true := (by decide : [8,6,115,105,122,101,39,48,1,16,1,0,0,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,10,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,11,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,12,3,105,39,49,1,16,0,0,0,0,0,0,13,3,105,39,48,1,16,0,0,0,0,0,0,14,9,98,121,116,101,95,114,101,97,100].all wordBound = true)

def C5_1p1 : List Nat := [1,8,0,0,0,0,0,0,15,4,36,52,39,51,1,16,0,0,0,0,0,0]
theorem C5_1p1bound : C5_1p1.all wordBound = true := (by decide : [1,8,0,0,0,0,0,0,15,4,36,52,39,51,1,16,0,0,0,0,0,0].all wordBound = true)

def C5_1words : List Nat := C5_1p0 ++ C5_1p1

theorem C5_1wire : C5_1.flatMap columnWords = C5_1words := by
  rfl

theorem C5_1wordBound : C5_1words.all wordBound = true := by
  simp only [C5_1words,List.all_append,C5_1p0bound,C5_1p1bound]
  try rfl

theorem C5_1bounded : ∀ n ∈ C5_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C5_1wordBound

theorem C5_1length : C5_1.length = 8 := by rfl

def C5_2 : List Column := [⟨16, [36,52,39,50], (some (16)), false, false, false⟩,⟨17, [36,52,39,49], (some (16)), false, false, false⟩,⟨18, [36,52,39,48], (some (16)), false, false, false⟩,⟨19, [108,99,109,36,53,39,49], (some (16)), false, false, false⟩,⟨20, [108,99,109,36,53,39,48], (some (16)), false, false, false⟩,⟨21, [108,99,109,36,54], (some (1)), false, false, false⟩,⟨22, [115,116,97,109,112,36,57,39,50], (some (16)), false, false, false⟩,⟨23, [115,116,97,109,112,36,57,39,49], (some (16)), false, false, false⟩]

def C5_2p0 : List Nat := [16,4,36,52,39,50,1,16,0,0,0,0,0,0,17,4,36,52,39,49,1,16,0,0,0,0,0,0,18,4,36,52,39,48,1,16,0,0,0,0,0,0,19,7,108,99,109,36,53,39,49,1,16,0,0,0,0,0,0,20,7,108,99,109,36,53,39,48,1,16,0,0,0,0,0,0,21,5,108,99,109,36,54,1,1,0,0,0,0,0,0,22,9,115,116,97,109,112,36,57,39,50,1,16,0,0,0,0,0,0,23,9,115,116,97,109,112,36,57,39,49,1,16,0,0,0,0,0]
theorem C5_2p0bound : C5_2p0.all wordBound = true := (by decide : [16,4,36,52,39,50,1,16,0,0,0,0,0,0,17,4,36,52,39,49,1,16,0,0,0,0,0,0,18,4,36,52,39,48,1,16,0,0,0,0,0,0,19,7,108,99,109,36,53,39,49,1,16,0,0,0,0,0,0,20,7,108,99,109,36,53,39,48,1,16,0,0,0,0,0,0,21,5,108,99,109,36,54,1,1,0,0,0,0,0,0,22,9,115,116,97,109,112,36,57,39,50,1,16,0,0,0,0,0,0,23,9,115,116,97,109,112,36,57,39,49,1,16,0,0,0,0,0].all wordBound = true)

def C5_2p1 : List Nat := [0]
theorem C5_2p1bound : C5_2p1.all wordBound = true := (by decide : [0].all wordBound = true)

def C5_2words : List Nat := C5_2p0 ++ C5_2p1

theorem C5_2wire : C5_2.flatMap columnWords = C5_2words := by
  rfl

theorem C5_2wordBound : C5_2words.all wordBound = true := by
  simp only [C5_2words,List.all_append,C5_2p0bound,C5_2p1bound]
  try rfl

theorem C5_2bounded : ∀ n ∈ C5_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C5_2wordBound

theorem C5_2length : C5_2.length = 8 := by rfl

def C5_3 : List Column := [⟨24, [115,116,97,109,112,36,57,39,48], (some (16)), false, false, false⟩,⟨25, [98,36,50,56], (some (1)), false, false, false⟩,⟨26, [98,36,50,57], (some (1)), false, false, false⟩,⟨27, [99,36,51,48], (some (1)), false, false, false⟩,⟨28, [99,36,51,49], (some (1)), false, false, false⟩,⟨29, [99,36,51,50], (some (1)), false, false, false⟩,⟨30, [99,36,51,56], (some (1)), false, false, false⟩,⟨31, [102,108,97,36,51,49], (some (16)), false, false, false⟩]

def C5_3p0 : List Nat := [24,9,115,116,97,109,112,36,57,39,48,1,16,0,0,0,0,0,0,25,4,98,36,50,56,1,1,0,0,0,0,0,0,26,4,98,36,50,57,1,1,0,0,0,0,0,0,27,4,99,36,51,48,1,1,0,0,0,0,0,0,28,4,99,36,51,49,1,1,0,0,0,0,0,0,29,4,99,36,51,50,1,1,0,0,0,0,0,0,30,4,99,36,51,56,1,1,0,0,0,0,0,0,31,6,102,108,97,36,51,49,1,16,0,0,0,0,0,0]
theorem C5_3p0bound : C5_3p0.all wordBound = true := (by decide : [24,9,115,116,97,109,112,36,57,39,48,1,16,0,0,0,0,0,0,25,4,98,36,50,56,1,1,0,0,0,0,0,0,26,4,98,36,50,57,1,1,0,0,0,0,0,0,27,4,99,36,51,48,1,1,0,0,0,0,0,0,28,4,99,36,51,49,1,1,0,0,0,0,0,0,29,4,99,36,51,50,1,1,0,0,0,0,0,0,30,4,99,36,51,56,1,1,0,0,0,0,0,0,31,6,102,108,97,36,51,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C5_3words : List Nat := C5_3p0

theorem C5_3wire : C5_3.flatMap columnWords = C5_3words := by
  rfl

theorem C5_3wordBound : C5_3words.all wordBound = true := by
  simp only [C5_3words,List.all_append,C5_3p0bound]
  try rfl

theorem C5_3bounded : ∀ n ∈ C5_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C5_3wordBound

theorem C5_3length : C5_3.length = 8 := by rfl

def C5_4 : List Column := [⟨32, [102,108,97,36,51,50], (some (16)), false, false, false⟩,⟨33, [102,108,97,36,51,51], (some (16)), false, false, false⟩,⟨34, [36,114,101,116], (some (1)), false, false, false⟩,⟨35, [36,112,99], (some (2)), false, false, false⟩,⟨36, [36,105,115,95,112,99,95,49], (some (1)), false, false, false⟩,⟨37, [36,105,115,95,112,99,95,50], (some (1)), false, false, false⟩,⟨38, [36,108,111,111,107,117,112,95,115,101,108,95,51,56], (some (1)), false, false, false⟩,⟨39, [36,108,111,111,107,117,112,95,115,101,108,95,51,57], (some (1)), false, false, false⟩]

def C5_4p0 : List Nat := [32,6,102,108,97,36,51,50,1,16,0,0,0,0,0,0,33,6,102,108,97,36,51,51,1,16,0,0,0,0,0,0,34,4,36,114,101,116,1,1,0,0,0,0,0,0,35,3,36,112,99,1,2,0,0,0,0,0,0,36,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,37,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,38,14,36,108,111,111,107,117,112,95,115,101,108,95,51,56,1,1,0,0,0,0,0,0,39,14,36,108,111,111,107,117,112]
theorem C5_4p0bound : C5_4p0.all wordBound = true := (by decide : [32,6,102,108,97,36,51,50,1,16,0,0,0,0,0,0,33,6,102,108,97,36,51,51,1,16,0,0,0,0,0,0,34,4,36,114,101,116,1,1,0,0,0,0,0,0,35,3,36,112,99,1,2,0,0,0,0,0,0,36,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,37,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,38,14,36,108,111,111,107,117,112,95,115,101,108,95,51,56,1,1,0,0,0,0,0,0,39,14,36,108,111,111,107,117,112].all wordBound = true)

def C5_4p1 : List Nat := [95,115,101,108,95,51,57,1,1,0,0,0,0,0,0]
theorem C5_4p1bound : C5_4p1.all wordBound = true := (by decide : [95,115,101,108,95,51,57,1,1,0,0,0,0,0,0].all wordBound = true)

def C5_4words : List Nat := C5_4p0 ++ C5_4p1

theorem C5_4wire : C5_4.flatMap columnWords = C5_4words := by
  rfl

theorem C5_4wordBound : C5_4words.all wordBound = true := by
  simp only [C5_4words,List.all_append,C5_4p0bound,C5_4p1bound]
  try rfl

theorem C5_4bounded : ∀ n ∈ C5_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C5_4wordBound

theorem C5_4length : C5_4.length = 8 := by rfl

def C5_5 : List Column := [⟨40, [40,105,110,118,32,119,114,105,116,101,95,111,117,116,112,117,116,58,36,112,99,41], none, false, false, true⟩]

def C5_5p0 : List Nat := [40,22,40,105,110,118,32,119,114,105,116,101,95,111,117,116,112,117,116,58,36,112,99,41,0,0,0,0,0,0,1,0]
theorem C5_5p0bound : C5_5p0.all wordBound = true := (by decide : [40,22,40,105,110,118,32,119,114,105,116,101,95,111,117,116,112,117,116,58,36,112,99,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C5_5words : List Nat := C5_5p0

theorem C5_5wire : C5_5.flatMap columnWords = C5_5words := by
  rfl

theorem C5_5wordBound : C5_5words.all wordBound = true := by
  simp only [C5_5words,List.all_append,C5_5p0bound]
  try rfl

theorem C5_5bounded : ∀ n ∈ C5_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C5_5wordBound

theorem C5_5length : C5_5.length = 1 := by rfl

def M5 : Module := ⟨5, [119,114,105,116,101,95,111,117,116,112,117,116], false, false, C5_0 ++ C5_1 ++ C5_2 ++ C5_3 ++ C5_4 ++ C5_5, ((List.range 0).map (fun n => [n]))⟩

def M5prefix : List Nat := [5,12,119,114,105,116,101,95,111,117,116,112,117,116,0,0,0,0,41]
theorem M5prefixwordBound : M5prefix.all wordBound = true := by decide

def M5words : List Nat := M5prefix ++ C5_0words ++ C5_1words ++ C5_2words ++ C5_3words ++ C5_4words ++ C5_5words ++ [0]

theorem M5wire : module.encode M5 = M5words := by
  rw [module_fast]
  simp only [M5,moduleWords,List.length_append,List.flatMap_append,C5_0length,C5_1length,C5_2length,C5_3length,C5_4length,C5_5length,C5_0wire,C5_1wire,C5_2wire,C5_3wire,C5_4wire,C5_5wire]
  rfl

theorem M5wordBound : M5words.all wordBound = true := by
  simp only [M5words,List.all_append,M5prefixwordBound,C5_0wordBound,C5_1wordBound,C5_2wordBound,C5_3wordBound,C5_4wordBound,C5_5wordBound]
  decide

theorem M5bounded : ∀ n ∈ M5words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M5wordBound

end DivRemFV.Replay
