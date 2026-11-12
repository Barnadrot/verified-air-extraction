import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C51_0 : List Column := [⟨0, [114,97,109,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨1, [114,97,109,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨2, [114,97,109,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨3, [97,100,100,114,101,115,115,39,51], (some (16)), true, false, false⟩,⟨4, [97,100,100,114,101,115,115,39,50], (some (16)), true, false, false⟩,⟨5, [97,100,100,114,101,115,115,39,49], (some (16)), true, false, false⟩,⟨6, [97,100,100,114,101,115,115,39,48], (some (16)), true, false, false⟩,⟨7, [118,97,108,117,101], (some (8)), true, false, false⟩]

def C51_0p0 : List Nat := [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115]
theorem C51_0p0bound : C51_0p0.all wordBound = true := (by decide : [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115].all wordBound = true)

def C51_0p1 : List Nat := [115,39,48,1,16,1,0,0,0,0,0,7,5,118,97,108,117,101,1,8,1,0,0,0,0,0]
theorem C51_0p1bound : C51_0p1.all wordBound = true := (by decide : [115,39,48,1,16,1,0,0,0,0,0,7,5,118,97,108,117,101,1,8,1,0,0,0,0,0].all wordBound = true)

def C51_0words : List Nat := C51_0p0 ++ C51_0p1

theorem C51_0wire : C51_0.flatMap columnWords = C51_0words := by
  rfl

theorem C51_0wordBound : C51_0words.all wordBound = true := by
  simp only [C51_0words,List.all_append,C51_0p0bound,C51_0p1bound]
  try rfl

theorem C51_0bounded : ∀ n ∈ C51_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C51_0wordBound

theorem C51_0length : C51_0.length = 8 := by rfl

def C51_1 : List Column := [⟨8, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,50], (some (16)), false, true, false⟩,⟨9, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨10, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨11, [98,111,102,102,115,101,116], (some (2)), false, false, false⟩,⟨12, [119,111,102,102,115,101,116,39,51], (some (14)), false, false, false⟩,⟨13, [119,111,102,102,115,101,116,39,50], (some (16)), false, false, false⟩,⟨14, [119,111,102,102,115,101,116,39,49], (some (16)), false, false, false⟩,⟨15, [119,111,102,102,115,101,116,39,48], (some (16)), false, false, false⟩]

def C51_1p0 : List Nat := [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,10,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,11,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,12,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0]
theorem C51_1p0bound : C51_1p0.all wordBound = true := (by decide : [8,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,10,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,11,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,12,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0].all wordBound = true)

def C51_1p1 : List Nat := [0,0,14,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0]
theorem C51_1p1bound : C51_1p1.all wordBound = true := (by decide : [0,0,14,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C51_1words : List Nat := C51_1p0 ++ C51_1p1

theorem C51_1wire : C51_1.flatMap columnWords = C51_1words := by
  rfl

theorem C51_1wordBound : C51_1words.all wordBound = true := by
  simp only [C51_1words,List.all_append,C51_1p0bound,C51_1p1bound]
  try rfl

theorem C51_1bounded : ∀ n ∈ C51_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C51_1wordBound

theorem C51_1length : C51_1.length = 8 := by rfl

def C51_2 : List Column := [⟨16, [116,109,112,48], (some (8)), false, false, false⟩,⟨17, [116,109,112,49], (some (8)), false, false, false⟩,⟨18, [116,109,112,50], (some (8)), false, false, false⟩,⟨19, [116,109,112,51], (some (8)), false, false, false⟩,⟨20, [119,111,114,100,39,49], (some (16)), false, false, false⟩,⟨21, [119,111,114,100,39,48], (some (16)), false, false, false⟩,⟨22, [36,57,39,49], (some (16)), false, false, false⟩,⟨23, [36,57,39,48], (some (16)), false, false, false⟩]

def C51_2p0 : List Nat := [16,4,116,109,112,48,1,8,0,0,0,0,0,0,17,4,116,109,112,49,1,8,0,0,0,0,0,0,18,4,116,109,112,50,1,8,0,0,0,0,0,0,19,4,116,109,112,51,1,8,0,0,0,0,0,0,20,6,119,111,114,100,39,49,1,16,0,0,0,0,0,0,21,6,119,111,114,100,39,48,1,16,0,0,0,0,0,0,22,4,36,57,39,49,1,16,0,0,0,0,0,0,23,4,36,57,39,48,1,16,0,0,0,0,0,0]
theorem C51_2p0bound : C51_2p0.all wordBound = true := (by decide : [16,4,116,109,112,48,1,8,0,0,0,0,0,0,17,4,116,109,112,49,1,8,0,0,0,0,0,0,18,4,116,109,112,50,1,8,0,0,0,0,0,0,19,4,116,109,112,51,1,8,0,0,0,0,0,0,20,6,119,111,114,100,39,49,1,16,0,0,0,0,0,0,21,6,119,111,114,100,39,48,1,16,0,0,0,0,0,0,22,4,36,57,39,49,1,16,0,0,0,0,0,0,23,4,36,57,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C51_2words : List Nat := C51_2p0

theorem C51_2wire : C51_2.flatMap columnWords = C51_2words := by
  rfl

theorem C51_2wordBound : C51_2words.all wordBound = true := by
  simp only [C51_2words,List.all_append,C51_2p0bound]
  try rfl

theorem C51_2bounded : ∀ n ∈ C51_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C51_2wordBound

theorem C51_2length : C51_2.length = 8 := by rfl

def C51_3 : List Column := [⟨24, [115,116,97,109,112,36,49,50,39,50], (some (16)), false, false, false⟩,⟨25, [115,116,97,109,112,36,49,50,39,49], (some (16)), false, false, false⟩,⟨26, [115,116,97,109,112,36,49,50,39,48], (some (16)), false, false, false⟩,⟨27, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,49], (some (1)), false, false, false⟩,⟨28, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,50], (some (1)), false, false, false⟩,⟨29, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,51], (some (1)), false, false, false⟩,⟨30, [108,115,119,36,49,54], (some (1)), false, false, false⟩,⟨31, [36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,100,101,102,97,117,108,116], (some (1)), false, false, false⟩]

def C51_3p0 : List Nat := [24,10,115,116,97,109,112,36,49,50,39,50,1,16,0,0,0,0,0,0,25,10,115,116,97,109,112,36,49,50,39,49,1,16,0,0,0,0,0,0,26,10,115,116,97,109,112,36,49,50,39,48,1,16,0,0,0,0,0,0,27,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,49,1,1,0,0,0,0,0,0,28,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,50,1,1,0,0,0,0,0,0,29,18,36,98,95,115,119,105,116,99,104,95]
theorem C51_3p0bound : C51_3p0.all wordBound = true := (by decide : [24,10,115,116,97,109,112,36,49,50,39,50,1,16,0,0,0,0,0,0,25,10,115,116,97,109,112,36,49,50,39,49,1,16,0,0,0,0,0,0,26,10,115,116,97,109,112,36,49,50,39,48,1,16,0,0,0,0,0,0,27,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,49,1,1,0,0,0,0,0,0,28,18,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,50,1,1,0,0,0,0,0,0,29,18,36,98,95,115,119,105,116,99,104,95].all wordBound = true)

def C51_3p1 : List Nat := [49,95,99,97,115,101,95,51,1,1,0,0,0,0,0,0,30,6,108,115,119,36,49,54,1,1,0,0,0,0,0,0,31,24,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,100,101,102,97,117,108,116,1,1,0,0,0,0,0,0]
theorem C51_3p1bound : C51_3p1.all wordBound = true := (by decide : [49,95,99,97,115,101,95,51,1,1,0,0,0,0,0,0,30,6,108,115,119,36,49,54,1,1,0,0,0,0,0,0,31,24,36,98,95,115,119,105,116,99,104,95,49,95,99,97,115,101,95,100,101,102,97,117,108,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C51_3words : List Nat := C51_3p0 ++ C51_3p1

theorem C51_3wire : C51_3.flatMap columnWords = C51_3words := by
  rfl

theorem C51_3wordBound : C51_3words.all wordBound = true := by
  simp only [C51_3words,List.all_append,C51_3p0bound,C51_3p1bound]
  try rfl

theorem C51_3bounded : ∀ n ∈ C51_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C51_3wordBound

theorem C51_3length : C51_3.length = 8 := by rfl

def C51_4 : List Column := [⟨32, [99,36,51,50], (some (14)), false, false, false⟩,⟨33, [99,36,51,51], (some (14)), false, false, false⟩,⟨34, [99,36,51,52], (some (14)), false, false, false⟩,⟨35, [99,36,51,53], (some (14)), false, false, false⟩,⟨36, [99,36,51,54], (some (1)), false, false, false⟩,⟨37, [99,36,51,55], (some (1)), false, false, false⟩,⟨38, [99,36,51,56], (some (8)), false, false, false⟩,⟨39, [99,36,52,50], (some (1)), false, false, false⟩]

def C51_4p0 : List Nat := [32,4,99,36,51,50,1,14,0,0,0,0,0,0,33,4,99,36,51,51,1,14,0,0,0,0,0,0,34,4,99,36,51,52,1,14,0,0,0,0,0,0,35,4,99,36,51,53,1,14,0,0,0,0,0,0,36,4,99,36,51,54,1,1,0,0,0,0,0,0,37,4,99,36,51,55,1,1,0,0,0,0,0,0,38,4,99,36,51,56,1,8,0,0,0,0,0,0,39,4,99,36,52,50,1,1,0,0,0,0,0,0]
theorem C51_4p0bound : C51_4p0.all wordBound = true := (by decide : [32,4,99,36,51,50,1,14,0,0,0,0,0,0,33,4,99,36,51,51,1,14,0,0,0,0,0,0,34,4,99,36,51,52,1,14,0,0,0,0,0,0,35,4,99,36,51,53,1,14,0,0,0,0,0,0,36,4,99,36,51,54,1,1,0,0,0,0,0,0,37,4,99,36,51,55,1,1,0,0,0,0,0,0,38,4,99,36,51,56,1,8,0,0,0,0,0,0,39,4,99,36,52,50,1,1,0,0,0,0,0,0].all wordBound = true)

def C51_4words : List Nat := C51_4p0

theorem C51_4wire : C51_4.flatMap columnWords = C51_4words := by
  rfl

theorem C51_4wordBound : C51_4words.all wordBound = true := by
  simp only [C51_4words,List.all_append,C51_4p0bound]
  try rfl

theorem C51_4bounded : ∀ n ∈ C51_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C51_4wordBound

theorem C51_4length : C51_4.length = 8 := by rfl

def C51_5 : List Column := [⟨40, [99,36,52,51], (some (1)), false, false, false⟩,⟨41, [36,114,101,116], (some (1)), false, false, false⟩,⟨42, [40,105,110,118,32,119,114,105,116,101,95,56,58,98,111,102,102,115,101,116,41], none, false, false, true⟩,⟨43, [40,105,110,118,32,40,45,32,119,114,105,116,101,95,56,58,98,111,102,102,115,101,116,32,49,41,41], none, false, false, true⟩,⟨44, [40,105,110,118,32,40,45,32,119,114,105,116,101,95,56,58,98,111,102,102,115,101,116,32,50,41,41], none, false, false, true⟩]

def C51_5p0 : List Nat := [40,4,99,36,52,51,1,1,0,0,0,0,0,0,41,4,36,114,101,116,1,1,0,0,0,0,0,0,42,21,40,105,110,118,32,119,114,105,116,101,95,56,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0,43,27,40,105,110,118,32,40,45,32,119,114,105,116,101,95,56,58,98,111,102,102,115,101,116,32,49,41,41,0,0,0,0,0,0,1,0,44,27,40,105,110,118,32,40,45,32,119,114,105,116,101,95,56,58,98,111,102,102,115,101,116,32,50,41,41,0,0,0]
theorem C51_5p0bound : C51_5p0.all wordBound = true := (by decide : [40,4,99,36,52,51,1,1,0,0,0,0,0,0,41,4,36,114,101,116,1,1,0,0,0,0,0,0,42,21,40,105,110,118,32,119,114,105,116,101,95,56,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0,43,27,40,105,110,118,32,40,45,32,119,114,105,116,101,95,56,58,98,111,102,102,115,101,116,32,49,41,41,0,0,0,0,0,0,1,0,44,27,40,105,110,118,32,40,45,32,119,114,105,116,101,95,56,58,98,111,102,102,115,101,116,32,50,41,41,0,0,0].all wordBound = true)

def C51_5p1 : List Nat := [0,0,0,1,0]
theorem C51_5p1bound : C51_5p1.all wordBound = true := (by decide : [0,0,0,1,0].all wordBound = true)

def C51_5words : List Nat := C51_5p0 ++ C51_5p1

theorem C51_5wire : C51_5.flatMap columnWords = C51_5words := by
  rfl

theorem C51_5wordBound : C51_5words.all wordBound = true := by
  simp only [C51_5words,List.all_append,C51_5p0bound,C51_5p1bound]
  try rfl

theorem C51_5bounded : ∀ n ∈ C51_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C51_5wordBound

theorem C51_5length : C51_5.length = 5 := by rfl

def M51 : Module := ⟨51, [119,114,105,116,101,95,56], false, false, C51_0 ++ C51_1 ++ C51_2 ++ C51_3 ++ C51_4 ++ C51_5, ((List.range 0).map (fun n => [n]))⟩

def M51prefix : List Nat := [51,7,119,114,105,116,101,95,56,0,0,0,0,45]
theorem M51prefixwordBound : M51prefix.all wordBound = true := by decide

def M51words : List Nat := M51prefix ++ C51_0words ++ C51_1words ++ C51_2words ++ C51_3words ++ C51_4words ++ C51_5words ++ [0]

theorem M51wire : module.encode M51 = M51words := by
  rw [module_fast]
  simp only [M51,moduleWords,List.length_append,List.flatMap_append,C51_0length,C51_1length,C51_2length,C51_3length,C51_4length,C51_5length,C51_0wire,C51_1wire,C51_2wire,C51_3wire,C51_4wire,C51_5wire]
  rfl

theorem M51wordBound : M51words.all wordBound = true := by
  simp only [M51words,List.all_append,M51prefixwordBound,C51_0wordBound,C51_1wordBound,C51_2wordBound,C51_3wordBound,C51_4wordBound,C51_5wordBound]
  decide

theorem M51bounded : ∀ n ∈ M51words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M51wordBound

end DivRemFV.Replay
