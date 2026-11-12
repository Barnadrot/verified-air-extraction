import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C53_0 : List Column := [⟨0, [114,97,109,36,115,116,97,109,112,39,50], (some (16)), true, false, false⟩,⟨1, [114,97,109,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨2, [114,97,109,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨3, [97,100,100,114,101,115,115,39,51], (some (16)), true, false, false⟩,⟨4, [97,100,100,114,101,115,115,39,50], (some (16)), true, false, false⟩,⟨5, [97,100,100,114,101,115,115,39,49], (some (16)), true, false, false⟩,⟨6, [97,100,100,114,101,115,115,39,48], (some (16)), true, false, false⟩,⟨7, [118,97,108,117,101,39,49], (some (16)), true, false, false⟩]

def C53_0p0 : List Nat := [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115]
theorem C53_0p0bound : C53_0p0.all wordBound = true := (by decide : [0,11,114,97,109,36,115,116,97,109,112,39,50,1,16,1,0,0,0,0,0,1,11,114,97,109,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,2,11,114,97,109,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,3,9,97,100,100,114,101,115,115,39,51,1,16,1,0,0,0,0,0,4,9,97,100,100,114,101,115,115,39,50,1,16,1,0,0,0,0,0,5,9,97,100,100,114,101,115,115,39,49,1,16,1,0,0,0,0,0,6,9,97,100,100,114,101,115].all wordBound = true)

def C53_0p1 : List Nat := [115,39,48,1,16,1,0,0,0,0,0,7,7,118,97,108,117,101,39,49,1,16,1,0,0,0,0,0]
theorem C53_0p1bound : C53_0p1.all wordBound = true := (by decide : [115,39,48,1,16,1,0,0,0,0,0,7,7,118,97,108,117,101,39,49,1,16,1,0,0,0,0,0].all wordBound = true)

def C53_0words : List Nat := C53_0p0 ++ C53_0p1

theorem C53_0wire : C53_0.flatMap columnWords = C53_0words := by
  rfl

theorem C53_0wordBound : C53_0words.all wordBound = true := by
  simp only [C53_0words,List.all_append,C53_0p0bound,C53_0p1bound]
  try rfl

theorem C53_0bounded : ∀ n ∈ C53_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C53_0wordBound

theorem C53_0length : C53_0.length = 8 := by rfl

def C53_1 : List Column := [⟨8, [118,97,108,117,101,39,48], (some (16)), true, false, false⟩,⟨9, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,50], (some (16)), false, true, false⟩,⟨10, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨11, [114,97,109,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨12, [98,111,102,102,115,101,116], (some (2)), false, false, false⟩,⟨13, [119,111,102,102,115,101,116,39,51], (some (14)), false, false, false⟩,⟨14, [119,111,102,102,115,101,116,39,50], (some (16)), false, false, false⟩,⟨15, [119,111,102,102,115,101,116,39,49], (some (16)), false, false, false⟩]

def C53_1p0 : List Nat := [8,7,118,97,108,117,101,39,48,1,16,1,0,0,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,10,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,11,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,12,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0]
theorem C53_1p0bound : C53_1p0.all wordBound = true := (by decide : [8,7,118,97,108,117,101,39,48,1,16,1,0,0,0,0,0,9,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,50,1,16,0,0,1,0,0,0,10,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,11,15,114,97,109,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,12,7,98,111,102,102,115,101,116,1,2,0,0,0,0,0,0,13,9,119,111,102,102,115,101,116,39,51,1,14,0,0,0,0,0,0].all wordBound = true)

def C53_1p1 : List Nat := [14,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0]
theorem C53_1p1bound : C53_1p1.all wordBound = true := (by decide : [14,9,119,111,102,102,115,101,116,39,50,1,16,0,0,0,0,0,0,15,9,119,111,102,102,115,101,116,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C53_1words : List Nat := C53_1p0 ++ C53_1p1

theorem C53_1wire : C53_1.flatMap columnWords = C53_1words := by
  rfl

theorem C53_1wordBound : C53_1words.all wordBound = true := by
  simp only [C53_1words,List.all_append,C53_1p0bound,C53_1p1bound]
  try rfl

theorem C53_1bounded : ∀ n ∈ C53_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C53_1wordBound

theorem C53_1length : C53_1.length = 8 := by rfl

def C53_2 : List Column := [⟨16, [119,111,102,102,115,101,116,39,48], (some (16)), false, false, false⟩,⟨17, [108,111], (some (16)), false, false, false⟩,⟨18, [104,105], (some (16)), false, false, false⟩,⟨19, [36,54,39,51], (some (16)), false, false, false⟩,⟨20, [36,54,39,50], (some (16)), false, false, false⟩,⟨21, [36,54,39,49], (some (16)), false, false, false⟩,⟨22, [36,54,39,48], (some (16)), false, false, false⟩,⟨23, [115,116,97,109,112,36,57,39,50], (some (16)), false, false, false⟩]

def C53_2p0 : List Nat := [16,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0,17,2,108,111,1,16,0,0,0,0,0,0,18,2,104,105,1,16,0,0,0,0,0,0,19,4,36,54,39,51,1,16,0,0,0,0,0,0,20,4,36,54,39,50,1,16,0,0,0,0,0,0,21,4,36,54,39,49,1,16,0,0,0,0,0,0,22,4,36,54,39,48,1,16,0,0,0,0,0,0,23,9,115,116,97,109,112,36,57,39,50,1,16,0,0,0,0,0,0]
theorem C53_2p0bound : C53_2p0.all wordBound = true := (by decide : [16,9,119,111,102,102,115,101,116,39,48,1,16,0,0,0,0,0,0,17,2,108,111,1,16,0,0,0,0,0,0,18,2,104,105,1,16,0,0,0,0,0,0,19,4,36,54,39,51,1,16,0,0,0,0,0,0,20,4,36,54,39,50,1,16,0,0,0,0,0,0,21,4,36,54,39,49,1,16,0,0,0,0,0,0,22,4,36,54,39,48,1,16,0,0,0,0,0,0,23,9,115,116,97,109,112,36,57,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C53_2words : List Nat := C53_2p0

theorem C53_2wire : C53_2.flatMap columnWords = C53_2words := by
  rfl

theorem C53_2wordBound : C53_2words.all wordBound = true := by
  simp only [C53_2words,List.all_append,C53_2p0bound]
  try rfl

theorem C53_2bounded : ∀ n ∈ C53_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C53_2wordBound

theorem C53_2length : C53_2.length = 8 := by rfl

def C53_3 : List Column := [⟨24, [115,116,97,109,112,36,57,39,49], (some (16)), false, false, false⟩,⟨25, [115,116,97,109,112,36,57,39,48], (some (16)), false, false, false⟩,⟨26, [115,116,97,109,112,36,49,48,39,50], (some (16)), false, false, false⟩,⟨27, [115,116,97,109,112,36,49,48,39,49], (some (16)), false, false, false⟩,⟨28, [115,116,97,109,112,36,49,48,39,48], (some (16)), false, false, false⟩,⟨29, [102,115,99,36,49,49], (some (1)), false, false, false⟩,⟨30, [99,36,51,48], (some (14)), false, false, false⟩,⟨31, [99,36,51,49], (some (14)), false, false, false⟩]

def C53_3p0 : List Nat := [24,9,115,116,97,109,112,36,57,39,49,1,16,0,0,0,0,0,0,25,9,115,116,97,109,112,36,57,39,48,1,16,0,0,0,0,0,0,26,10,115,116,97,109,112,36,49,48,39,50,1,16,0,0,0,0,0,0,27,10,115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0,28,10,115,116,97,109,112,36,49,48,39,48,1,16,0,0,0,0,0,0,29,6,102,115,99,36,49,49,1,1,0,0,0,0,0,0,30,4,99,36,51,48,1,14,0,0,0,0,0,0]
theorem C53_3p0bound : C53_3p0.all wordBound = true := (by decide : [24,9,115,116,97,109,112,36,57,39,49,1,16,0,0,0,0,0,0,25,9,115,116,97,109,112,36,57,39,48,1,16,0,0,0,0,0,0,26,10,115,116,97,109,112,36,49,48,39,50,1,16,0,0,0,0,0,0,27,10,115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0,28,10,115,116,97,109,112,36,49,48,39,48,1,16,0,0,0,0,0,0,29,6,102,115,99,36,49,49,1,1,0,0,0,0,0,0,30,4,99,36,51,48,1,14,0,0,0,0,0,0].all wordBound = true)

def C53_3p1 : List Nat := [31,4,99,36,51,49,1,14,0,0,0,0,0,0]
theorem C53_3p1bound : C53_3p1.all wordBound = true := (by decide : [31,4,99,36,51,49,1,14,0,0,0,0,0,0].all wordBound = true)

def C53_3words : List Nat := C53_3p0 ++ C53_3p1

theorem C53_3wire : C53_3.flatMap columnWords = C53_3words := by
  rfl

theorem C53_3wordBound : C53_3words.all wordBound = true := by
  simp only [C53_3words,List.all_append,C53_3p0bound,C53_3p1bound]
  try rfl

theorem C53_3bounded : ∀ n ∈ C53_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C53_3wordBound

theorem C53_3length : C53_3.length = 8 := by rfl

def C53_4 : List Column := [⟨32, [99,36,51,50], (some (14)), false, false, false⟩,⟨33, [99,36,51,51], (some (14)), false, false, false⟩,⟨34, [99,36,51,52], (some (1)), false, false, false⟩,⟨35, [99,36,51,53], (some (1)), false, false, false⟩,⟨36, [99,36,51,56], (some (1)), false, false, false⟩,⟨37, [36,114,101,116], (some (1)), false, false, false⟩,⟨38, [36,108,111,111,107,117,112,95,115,101,108,95,51,56], (some (1)), false, false, false⟩,⟨39, [36,108,111,111,107,117,112,95,115,101,108,95,51,57], (some (1)), false, false, false⟩]

def C53_4p0 : List Nat := [32,4,99,36,51,50,1,14,0,0,0,0,0,0,33,4,99,36,51,51,1,14,0,0,0,0,0,0,34,4,99,36,51,52,1,1,0,0,0,0,0,0,35,4,99,36,51,53,1,1,0,0,0,0,0,0,36,4,99,36,51,56,1,1,0,0,0,0,0,0,37,4,36,114,101,116,1,1,0,0,0,0,0,0,38,14,36,108,111,111,107,117,112,95,115,101,108,95,51,56,1,1,0,0,0,0,0,0,39,14,36,108,111,111,107,117,112,95,115,101,108,95,51,57,1,1,0,0]
theorem C53_4p0bound : C53_4p0.all wordBound = true := (by decide : [32,4,99,36,51,50,1,14,0,0,0,0,0,0,33,4,99,36,51,51,1,14,0,0,0,0,0,0,34,4,99,36,51,52,1,1,0,0,0,0,0,0,35,4,99,36,51,53,1,1,0,0,0,0,0,0,36,4,99,36,51,56,1,1,0,0,0,0,0,0,37,4,36,114,101,116,1,1,0,0,0,0,0,0,38,14,36,108,111,111,107,117,112,95,115,101,108,95,51,56,1,1,0,0,0,0,0,0,39,14,36,108,111,111,107,117,112,95,115,101,108,95,51,57,1,1,0,0].all wordBound = true)

def C53_4p1 : List Nat := [0,0,0,0]
theorem C53_4p1bound : C53_4p1.all wordBound = true := (by decide : [0,0,0,0].all wordBound = true)

def C53_4words : List Nat := C53_4p0 ++ C53_4p1

theorem C53_4wire : C53_4.flatMap columnWords = C53_4words := by
  rfl

theorem C53_4wordBound : C53_4words.all wordBound = true := by
  simp only [C53_4words,List.all_append,C53_4p0bound,C53_4p1bound]
  try rfl

theorem C53_4bounded : ∀ n ∈ C53_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C53_4wordBound

theorem C53_4length : C53_4.length = 8 := by rfl

def C53_5 : List Column := [⟨40, [40,105,110,118,32,119,114,105,116,101,95,51,50,58,98,111,102,102,115,101,116,41], none, false, false, true⟩]

def C53_5p0 : List Nat := [40,22,40,105,110,118,32,119,114,105,116,101,95,51,50,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0]
theorem C53_5p0bound : C53_5p0.all wordBound = true := (by decide : [40,22,40,105,110,118,32,119,114,105,116,101,95,51,50,58,98,111,102,102,115,101,116,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C53_5words : List Nat := C53_5p0

theorem C53_5wire : C53_5.flatMap columnWords = C53_5words := by
  rfl

theorem C53_5wordBound : C53_5words.all wordBound = true := by
  simp only [C53_5words,List.all_append,C53_5p0bound]
  try rfl

theorem C53_5bounded : ∀ n ∈ C53_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C53_5wordBound

theorem C53_5length : C53_5.length = 1 := by rfl

def M53 : Module := ⟨53, [119,114,105,116,101,95,51,50], false, false, C53_0 ++ C53_1 ++ C53_2 ++ C53_3 ++ C53_4 ++ C53_5, ((List.range 0).map (fun n => [n]))⟩

def M53prefix : List Nat := [53,8,119,114,105,116,101,95,51,50,0,0,0,0,41]
theorem M53prefixwordBound : M53prefix.all wordBound = true := by decide

def M53words : List Nat := M53prefix ++ C53_0words ++ C53_1words ++ C53_2words ++ C53_3words ++ C53_4words ++ C53_5words ++ [0]

theorem M53wire : module.encode M53 = M53words := by
  rw [module_fast]
  simp only [M53,moduleWords,List.length_append,List.flatMap_append,C53_0length,C53_1length,C53_2length,C53_3length,C53_4length,C53_5length,C53_0wire,C53_1wire,C53_2wire,C53_3wire,C53_4wire,C53_5wire]
  rfl

theorem M53wordBound : M53words.all wordBound = true := by
  simp only [M53words,List.all_append,M53prefixwordBound,C53_0wordBound,C53_1wordBound,C53_2wordBound,C53_3wordBound,C53_4wordBound,C53_5wordBound]
  decide

theorem M53bounded : ∀ n ∈ M53words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M53wordBound

end DivRemFV.Replay
