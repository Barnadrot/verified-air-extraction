import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C57_0 : List Column := [⟨0, [108,104,115,39,49], (some (16)), true, false, false⟩,⟨1, [108,104,115,39,48], (some (16)), true, false, false⟩,⟨2, [114,104,115,39,49], (some (16)), true, false, false⟩,⟨3, [114,104,115,39,48], (some (16)), true, false, false⟩,⟨4, [104,105,39,49], (some (16)), false, true, false⟩,⟨5, [104,105,39,48], (some (16)), false, true, false⟩,⟨6, [108,111,39,49], (some (16)), false, true, false⟩,⟨7, [108,111,39,48], (some (16)), false, true, false⟩]

def C57_0p0 : List Nat := [0,5,108,104,115,39,49,1,16,1,0,0,0,0,0,1,5,108,104,115,39,48,1,16,1,0,0,0,0,0,2,5,114,104,115,39,49,1,16,1,0,0,0,0,0,3,5,114,104,115,39,48,1,16,1,0,0,0,0,0,4,4,104,105,39,49,1,16,0,0,1,0,0,0,5,4,104,105,39,48,1,16,0,0,1,0,0,0,6,4,108,111,39,49,1,16,0,0,1,0,0,0,7,4,108,111,39,48,1,16,0,0,1,0,0,0]
theorem C57_0p0bound : C57_0p0.all wordBound = true := (by decide : [0,5,108,104,115,39,49,1,16,1,0,0,0,0,0,1,5,108,104,115,39,48,1,16,1,0,0,0,0,0,2,5,114,104,115,39,49,1,16,1,0,0,0,0,0,3,5,114,104,115,39,48,1,16,1,0,0,0,0,0,4,4,104,105,39,49,1,16,0,0,1,0,0,0,5,4,104,105,39,48,1,16,0,0,1,0,0,0,6,4,108,111,39,49,1,16,0,0,1,0,0,0,7,4,108,111,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C57_0words : List Nat := C57_0p0

theorem C57_0wire : C57_0.flatMap columnWords = C57_0words := by
  rfl

theorem C57_0wordBound : C57_0words.all wordBound = true := by
  simp only [C57_0words,List.all_append,C57_0p0bound]
  try rfl

theorem C57_0bounded : ∀ n ∈ C57_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C57_0wordBound

theorem C57_0length : C57_0.length = 8 := by rfl

def C57_1 : List Column := [⟨8, [115,36,56], (some (15)), false, false, false⟩,⟨9, [115,36,57], (some (1)), false, false, false⟩,⟨10, [115,36,49,48], (some (14)), false, false, false⟩,⟨11, [115,36,49,49], (some (2)), false, false, false⟩,⟨12, [115,36,49,50], (some (15)), false, false, false⟩,⟨13, [115,36,49,51], (some (15)), false, false, false⟩,⟨14, [115,36,49,52], (some (1)), false, false, false⟩,⟨15, [115,36,49,53], (some (14)), false, false, false⟩]

def C57_1p0 : List Nat := [8,3,115,36,56,1,15,0,0,0,0,0,0,9,3,115,36,57,1,1,0,0,0,0,0,0,10,4,115,36,49,48,1,14,0,0,0,0,0,0,11,4,115,36,49,49,1,2,0,0,0,0,0,0,12,4,115,36,49,50,1,15,0,0,0,0,0,0,13,4,115,36,49,51,1,15,0,0,0,0,0,0,14,4,115,36,49,52,1,1,0,0,0,0,0,0,15,4,115,36,49,53,1,14,0,0,0,0,0,0]
theorem C57_1p0bound : C57_1p0.all wordBound = true := (by decide : [8,3,115,36,56,1,15,0,0,0,0,0,0,9,3,115,36,57,1,1,0,0,0,0,0,0,10,4,115,36,49,48,1,14,0,0,0,0,0,0,11,4,115,36,49,49,1,2,0,0,0,0,0,0,12,4,115,36,49,50,1,15,0,0,0,0,0,0,13,4,115,36,49,51,1,15,0,0,0,0,0,0,14,4,115,36,49,52,1,1,0,0,0,0,0,0,15,4,115,36,49,53,1,14,0,0,0,0,0,0].all wordBound = true)

def C57_1words : List Nat := C57_1p0

theorem C57_1wire : C57_1.flatMap columnWords = C57_1words := by
  rfl

theorem C57_1wordBound : C57_1words.all wordBound = true := by
  simp only [C57_1words,List.all_append,C57_1p0bound]
  try rfl

theorem C57_1bounded : ∀ n ∈ C57_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C57_1wordBound

theorem C57_1length : C57_1.length = 8 := by rfl

def C57_2 : List Column := [⟨16, [115,36,49,54], (some (2)), false, false, false⟩,⟨17, [115,36,49,55], (some (15)), false, false, false⟩,⟨18, [112,112,36,49,56], (some (15)), false, false, false⟩,⟨19, [112,112,36,49,57], (some (15)), false, false, false⟩,⟨20, [112,112,36,50,48], (some (15)), false, false, false⟩,⟨21, [112,112,36,50,49], (some (15)), false, false, false⟩,⟨22, [112,112,36,50,50], (some (15)), false, false, false⟩,⟨23, [112,112,36,50,51], (some (2)), false, false, false⟩]

def C57_2p0 : List Nat := [16,4,115,36,49,54,1,2,0,0,0,0,0,0,17,4,115,36,49,55,1,15,0,0,0,0,0,0,18,5,112,112,36,49,56,1,15,0,0,0,0,0,0,19,5,112,112,36,49,57,1,15,0,0,0,0,0,0,20,5,112,112,36,50,48,1,15,0,0,0,0,0,0,21,5,112,112,36,50,49,1,15,0,0,0,0,0,0,22,5,112,112,36,50,50,1,15,0,0,0,0,0,0,23,5,112,112,36,50,51,1,2,0,0,0,0,0,0]
theorem C57_2p0bound : C57_2p0.all wordBound = true := (by decide : [16,4,115,36,49,54,1,2,0,0,0,0,0,0,17,4,115,36,49,55,1,15,0,0,0,0,0,0,18,5,112,112,36,49,56,1,15,0,0,0,0,0,0,19,5,112,112,36,49,57,1,15,0,0,0,0,0,0,20,5,112,112,36,50,48,1,15,0,0,0,0,0,0,21,5,112,112,36,50,49,1,15,0,0,0,0,0,0,22,5,112,112,36,50,50,1,15,0,0,0,0,0,0,23,5,112,112,36,50,51,1,2,0,0,0,0,0,0].all wordBound = true)

def C57_2words : List Nat := C57_2p0

theorem C57_2wire : C57_2.flatMap columnWords = C57_2words := by
  rfl

theorem C57_2wordBound : C57_2words.all wordBound = true := by
  simp only [C57_2words,List.all_append,C57_2p0bound]
  try rfl

theorem C57_2bounded : ∀ n ∈ C57_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C57_2wordBound

theorem C57_2length : C57_2.length = 8 := by rfl

def C57_3 : List Column := [⟨24, [112,112,36,50,52], (some (15)), false, false, false⟩,⟨25, [112,112,36,50,53], (some (15)), false, false, false⟩,⟨26, [112,112,36,50,54], (some (15)), false, false, false⟩,⟨27, [112,112,36,50,55], (some (15)), false, false, false⟩,⟨28, [112,112,36,50,56], (some (15)), false, false, false⟩,⟨29, [112,112,36,50,57], (some (2)), false, false, false⟩,⟨30, [112,112,36,51,48], (some (15)), false, false, false⟩,⟨31, [112,112,36,51,49], (some (2)), false, false, false⟩]

def C57_3p0 : List Nat := [24,5,112,112,36,50,52,1,15,0,0,0,0,0,0,25,5,112,112,36,50,53,1,15,0,0,0,0,0,0,26,5,112,112,36,50,54,1,15,0,0,0,0,0,0,27,5,112,112,36,50,55,1,15,0,0,0,0,0,0,28,5,112,112,36,50,56,1,15,0,0,0,0,0,0,29,5,112,112,36,50,57,1,2,0,0,0,0,0,0,30,5,112,112,36,51,48,1,15,0,0,0,0,0,0,31,5,112,112,36,51,49,1,2,0,0,0,0,0,0]
theorem C57_3p0bound : C57_3p0.all wordBound = true := (by decide : [24,5,112,112,36,50,52,1,15,0,0,0,0,0,0,25,5,112,112,36,50,53,1,15,0,0,0,0,0,0,26,5,112,112,36,50,54,1,15,0,0,0,0,0,0,27,5,112,112,36,50,55,1,15,0,0,0,0,0,0,28,5,112,112,36,50,56,1,15,0,0,0,0,0,0,29,5,112,112,36,50,57,1,2,0,0,0,0,0,0,30,5,112,112,36,51,48,1,15,0,0,0,0,0,0,31,5,112,112,36,51,49,1,2,0,0,0,0,0,0].all wordBound = true)

def C57_3words : List Nat := C57_3p0

theorem C57_3wire : C57_3.flatMap columnWords = C57_3words := by
  rfl

theorem C57_3wordBound : C57_3words.all wordBound = true := by
  simp only [C57_3words,List.all_append,C57_3p0bound]
  try rfl

theorem C57_3bounded : ∀ n ∈ C57_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C57_3wordBound

theorem C57_3length : C57_3.length = 8 := by rfl

def C57_4 : List Column := [⟨32, [112,112,36,51,50], (some (15)), false, false, false⟩,⟨33, [112,112,36,51,51], (some (2)), false, false, false⟩,⟨34, [112,112,36,51,52], (some (4)), false, false, false⟩,⟨35, [109,36,51,53], (some (1)), false, false, false⟩,⟨36, [109,36,51,54], (some (14)), false, false, false⟩,⟨37, [99,36,51,55], (some (2)), false, false, false⟩,⟨38, [109,36,51,56], (some (2)), false, false, false⟩,⟨39, [109,36,51,57], (some (13)), false, false, false⟩]

def C57_4p0 : List Nat := [32,5,112,112,36,51,50,1,15,0,0,0,0,0,0,33,5,112,112,36,51,51,1,2,0,0,0,0,0,0,34,5,112,112,36,51,52,1,4,0,0,0,0,0,0,35,4,109,36,51,53,1,1,0,0,0,0,0,0,36,4,109,36,51,54,1,14,0,0,0,0,0,0,37,4,99,36,51,55,1,2,0,0,0,0,0,0,38,4,109,36,51,56,1,2,0,0,0,0,0,0,39,4,109,36,51,57,1,13,0,0,0,0,0,0]
theorem C57_4p0bound : C57_4p0.all wordBound = true := (by decide : [32,5,112,112,36,51,50,1,15,0,0,0,0,0,0,33,5,112,112,36,51,51,1,2,0,0,0,0,0,0,34,5,112,112,36,51,52,1,4,0,0,0,0,0,0,35,4,109,36,51,53,1,1,0,0,0,0,0,0,36,4,109,36,51,54,1,14,0,0,0,0,0,0,37,4,99,36,51,55,1,2,0,0,0,0,0,0,38,4,109,36,51,56,1,2,0,0,0,0,0,0,39,4,109,36,51,57,1,13,0,0,0,0,0,0].all wordBound = true)

def C57_4words : List Nat := C57_4p0

theorem C57_4wire : C57_4.flatMap columnWords = C57_4words := by
  rfl

theorem C57_4wordBound : C57_4words.all wordBound = true := by
  simp only [C57_4words,List.all_append,C57_4p0bound]
  try rfl

theorem C57_4bounded : ∀ n ∈ C57_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C57_4wordBound

theorem C57_4length : C57_4.length = 8 := by rfl

def C57_5 : List Column := [⟨40, [99,36,52,48], (some (3)), false, false, false⟩,⟨41, [109,36,52,49], (some (3)), false, false, false⟩,⟨42, [109,36,52,50], (some (12)), false, false, false⟩,⟨43, [99,36,52,51], (some (2)), false, false, false⟩,⟨44, [109,36,52,52], (some (4)), false, false, false⟩,⟨45, [36,114,101,116], (some (1)), false, false, false⟩]

def C57_5p0 : List Nat := [40,4,99,36,52,48,1,3,0,0,0,0,0,0,41,4,109,36,52,49,1,3,0,0,0,0,0,0,42,4,109,36,52,50,1,12,0,0,0,0,0,0,43,4,99,36,52,51,1,2,0,0,0,0,0,0,44,4,109,36,52,52,1,4,0,0,0,0,0,0,45,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C57_5p0bound : C57_5p0.all wordBound = true := (by decide : [40,4,99,36,52,48,1,3,0,0,0,0,0,0,41,4,109,36,52,49,1,3,0,0,0,0,0,0,42,4,109,36,52,50,1,12,0,0,0,0,0,0,43,4,99,36,52,51,1,2,0,0,0,0,0,0,44,4,109,36,52,52,1,4,0,0,0,0,0,0,45,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C57_5words : List Nat := C57_5p0

theorem C57_5wire : C57_5.flatMap columnWords = C57_5words := by
  rfl

theorem C57_5wordBound : C57_5words.all wordBound = true := by
  simp only [C57_5words,List.all_append,C57_5p0bound]
  try rfl

theorem C57_5bounded : ∀ n ∈ C57_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C57_5wordBound

theorem C57_5length : C57_5.length = 6 := by rfl

def M57 : Module := ⟨57, [109,117,108,51,50,95,117,117], false, false, C57_0 ++ C57_1 ++ C57_2 ++ C57_3 ++ C57_4 ++ C57_5, ((List.range 0).map (fun n => [n]))⟩

def M57prefix : List Nat := [57,8,109,117,108,51,50,95,117,117,0,0,0,0,46]
theorem M57prefixwordBound : M57prefix.all wordBound = true := by decide

def M57words : List Nat := M57prefix ++ C57_0words ++ C57_1words ++ C57_2words ++ C57_3words ++ C57_4words ++ C57_5words ++ [0]

theorem M57wire : module.encode M57 = M57words := by
  rw [module_fast]
  simp only [M57,moduleWords,List.length_append,List.flatMap_append,C57_0length,C57_1length,C57_2length,C57_3length,C57_4length,C57_5length,C57_0wire,C57_1wire,C57_2wire,C57_3wire,C57_4wire,C57_5wire]
  rfl

theorem M57wordBound : M57words.all wordBound = true := by
  simp only [M57words,List.all_append,M57prefixwordBound,C57_0wordBound,C57_1wordBound,C57_2wordBound,C57_3wordBound,C57_4wordBound,C57_5wordBound]
  decide

theorem M57bounded : ∀ n ∈ M57words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M57wordBound

end DivRemFV.Replay
