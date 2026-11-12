import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C77_0 : List Column := [⟨0, [97,114,103,49,39,51], (some (16)), true, false, false⟩,⟨1, [97,114,103,49,39,50], (some (16)), true, false, false⟩,⟨2, [97,114,103,49,39,49], (some (16)), true, false, false⟩,⟨3, [97,114,103,49,39,48], (some (16)), true, false, false⟩,⟨4, [97,114,103,50], (some (3)), true, false, false⟩,⟨5, [111,117,116,95,115,104,108,39,51], (some (16)), false, true, false⟩,⟨6, [111,117,116,95,115,104,108,39,50], (some (16)), false, true, false⟩,⟨7, [111,117,116,95,115,104,108,39,49], (some (16)), false, true, false⟩]

def C77_0p0 : List Nat := [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,3,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1]
theorem C77_0p0bound : C77_0p0.all wordBound = true := (by decide : [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,3,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1].all wordBound = true)

def C77_0p1 : List Nat := [16,0,0,1,0,0,0]
theorem C77_0p1bound : C77_0p1.all wordBound = true := (by decide : [16,0,0,1,0,0,0].all wordBound = true)

def C77_0words : List Nat := C77_0p0 ++ C77_0p1

theorem C77_0wire : C77_0.flatMap columnWords = C77_0words := by
  rfl

theorem C77_0wordBound : C77_0words.all wordBound = true := by
  simp only [C77_0words,List.all_append,C77_0p0bound,C77_0p1bound]
  try rfl

theorem C77_0bounded : ∀ n ∈ C77_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C77_0wordBound

theorem C77_0length : C77_0.length = 8 := by rfl

def C77_1 : List Column := [⟨8, [111,117,116,95,115,104,108,39,48], (some (16)), false, true, false⟩,⟨9, [111,117,116,95,115,104,114,39,51], (some (16)), false, true, false⟩,⟨10, [111,117,116,95,115,104,114,39,50], (some (16)), false, true, false⟩,⟨11, [111,117,116,95,115,104,114,39,49], (some (16)), false, true, false⟩,⟨12, [111,117,116,95,115,104,114,39,48], (some (16)), false, true, false⟩,⟨13, [36,110,108,111,119,48], (some (2)), false, false, false⟩,⟨14, [36,98,105,116,49], (some (1)), false, false, false⟩,⟨15, [36,108,111,95,115,104,108,50,39,51], (some (16)), false, false, false⟩]

def C77_1p0 : List Nat := [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,110,108,111,119,48,1,2,0,0,0,0,0,0,14,5,36,98,105,116,49,1,1,0,0,0,0,0,0,15,10]
theorem C77_1p0bound : C77_1p0.all wordBound = true := (by decide : [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,110,108,111,119,48,1,2,0,0,0,0,0,0,14,5,36,98,105,116,49,1,1,0,0,0,0,0,0,15,10].all wordBound = true)

def C77_1p1 : List Nat := [36,108,111,95,115,104,108,50,39,51,1,16,0,0,0,0,0,0]
theorem C77_1p1bound : C77_1p1.all wordBound = true := (by decide : [36,108,111,95,115,104,108,50,39,51,1,16,0,0,0,0,0,0].all wordBound = true)

def C77_1words : List Nat := C77_1p0 ++ C77_1p1

theorem C77_1wire : C77_1.flatMap columnWords = C77_1words := by
  rfl

theorem C77_1wordBound : C77_1words.all wordBound = true := by
  simp only [C77_1words,List.all_append,C77_1p0bound,C77_1p1bound]
  try rfl

theorem C77_1bounded : ∀ n ∈ C77_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C77_1wordBound

theorem C77_1length : C77_1.length = 8 := by rfl

def C77_2 : List Column := [⟨16, [36,108,111,95,115,104,108,50,39,50], (some (16)), false, false, false⟩,⟨17, [36,108,111,95,115,104,108,50,39,49], (some (16)), false, false, false⟩,⟨18, [36,108,111,95,115,104,108,50,39,48], (some (16)), false, false, false⟩,⟨19, [36,108,111,95,115,104,114,51,39,51], (some (16)), false, false, false⟩,⟨20, [36,108,111,95,115,104,114,51,39,50], (some (16)), false, false, false⟩,⟨21, [36,108,111,95,115,104,114,51,39,49], (some (16)), false, false, false⟩,⟨22, [36,108,111,95,115,104,114,51,39,48], (some (16)), false, false, false⟩,⟨23, [36,100,114,111,112,52], (some (4)), false, false, false⟩]

def C77_2p0 : List Nat := [16,10,36,108,111,95,115,104,108,50,39,50,1,16,0,0,0,0,0,0,17,10,36,108,111,95,115,104,108,50,39,49,1,16,0,0,0,0,0,0,18,10,36,108,111,95,115,104,108,50,39,48,1,16,0,0,0,0,0,0,19,10,36,108,111,95,115,104,114,51,39,51,1,16,0,0,0,0,0,0,20,10,36,108,111,95,115,104,114,51,39,50,1,16,0,0,0,0,0,0,21,10,36,108,111,95,115,104,114,51,39,49,1,16,0,0,0,0,0,0,22,10,36,108,111,95,115,104]
theorem C77_2p0bound : C77_2p0.all wordBound = true := (by decide : [16,10,36,108,111,95,115,104,108,50,39,50,1,16,0,0,0,0,0,0,17,10,36,108,111,95,115,104,108,50,39,49,1,16,0,0,0,0,0,0,18,10,36,108,111,95,115,104,108,50,39,48,1,16,0,0,0,0,0,0,19,10,36,108,111,95,115,104,114,51,39,51,1,16,0,0,0,0,0,0,20,10,36,108,111,95,115,104,114,51,39,50,1,16,0,0,0,0,0,0,21,10,36,108,111,95,115,104,114,51,39,49,1,16,0,0,0,0,0,0,22,10,36,108,111,95,115,104].all wordBound = true)

def C77_2p1 : List Nat := [114,51,39,48,1,16,0,0,0,0,0,0,23,6,36,100,114,111,112,52,1,4,0,0,0,0,0,0]
theorem C77_2p1bound : C77_2p1.all wordBound = true := (by decide : [114,51,39,48,1,16,0,0,0,0,0,0,23,6,36,100,114,111,112,52,1,4,0,0,0,0,0,0].all wordBound = true)

def C77_2words : List Nat := C77_2p0 ++ C77_2p1

theorem C77_2wire : C77_2.flatMap columnWords = C77_2words := by
  rfl

theorem C77_2wordBound : C77_2words.all wordBound = true := by
  simp only [C77_2words,List.all_append,C77_2p0bound,C77_2p1bound]
  try rfl

theorem C77_2bounded : ∀ n ∈ C77_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C77_2wordBound

theorem C77_2length : C77_2.length = 8 := by rfl

def C77_3 : List Column := [⟨24, [36,107,101,101,112,53,39,51], (some (12)), false, false, false⟩,⟨25, [36,107,101,101,112,53,39,50], (some (16)), false, false, false⟩,⟨26, [36,107,101,101,112,53,39,49], (some (16)), false, false, false⟩,⟨27, [36,107,101,101,112,53,39,48], (some (16)), false, false, false⟩,⟨28, [36,122,101,114,111,115,54], (some (4)), false, false, false⟩,⟨29, [36,100,114,111,112,55], (some (4)), false, false, false⟩,⟨30, [36,107,101,101,112,56,39,51], (some (12)), false, false, false⟩,⟨31, [36,107,101,101,112,56,39,50], (some (16)), false, false, false⟩]

def C77_3p0 : List Nat := [24,8,36,107,101,101,112,53,39,51,1,12,0,0,0,0,0,0,25,8,36,107,101,101,112,53,39,50,1,16,0,0,0,0,0,0,26,8,36,107,101,101,112,53,39,49,1,16,0,0,0,0,0,0,27,8,36,107,101,101,112,53,39,48,1,16,0,0,0,0,0,0,28,7,36,122,101,114,111,115,54,1,4,0,0,0,0,0,0,29,6,36,100,114,111,112,55,1,4,0,0,0,0,0,0,30,8,36,107,101,101,112,56,39,51,1,12,0,0,0,0,0,0,31,8,36,107,101]
theorem C77_3p0bound : C77_3p0.all wordBound = true := (by decide : [24,8,36,107,101,101,112,53,39,51,1,12,0,0,0,0,0,0,25,8,36,107,101,101,112,53,39,50,1,16,0,0,0,0,0,0,26,8,36,107,101,101,112,53,39,49,1,16,0,0,0,0,0,0,27,8,36,107,101,101,112,53,39,48,1,16,0,0,0,0,0,0,28,7,36,122,101,114,111,115,54,1,4,0,0,0,0,0,0,29,6,36,100,114,111,112,55,1,4,0,0,0,0,0,0,30,8,36,107,101,101,112,56,39,51,1,12,0,0,0,0,0,0,31,8,36,107,101].all wordBound = true)

def C77_3p1 : List Nat := [101,112,56,39,50,1,16,0,0,0,0,0,0]
theorem C77_3p1bound : C77_3p1.all wordBound = true := (by decide : [101,112,56,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C77_3words : List Nat := C77_3p0 ++ C77_3p1

theorem C77_3wire : C77_3.flatMap columnWords = C77_3words := by
  rfl

theorem C77_3wordBound : C77_3words.all wordBound = true := by
  simp only [C77_3words,List.all_append,C77_3p0bound,C77_3p1bound]
  try rfl

theorem C77_3bounded : ∀ n ∈ C77_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C77_3wordBound

theorem C77_3length : C77_3.length = 8 := by rfl

def C77_4 : List Column := [⟨32, [36,107,101,101,112,56,39,49], (some (16)), false, false, false⟩,⟨33, [36,107,101,101,112,56,39,48], (some (16)), false, false, false⟩,⟨34, [99,36,51,52], (some (4)), false, false, false⟩,⟨35, [99,36,51,53], (some (4)), false, false, false⟩,⟨36, [99,36,51,54], (some (16)), false, false, false⟩,⟨37, [116,36,51,55], (some (12)), false, false, false⟩,⟨38, [116,36,51,56], (some (4)), false, false, false⟩,⟨39, [116,36,51,57], (some (12)), false, false, false⟩]

def C77_4p0 : List Nat := [32,8,36,107,101,101,112,56,39,49,1,16,0,0,0,0,0,0,33,8,36,107,101,101,112,56,39,48,1,16,0,0,0,0,0,0,34,4,99,36,51,52,1,4,0,0,0,0,0,0,35,4,99,36,51,53,1,4,0,0,0,0,0,0,36,4,99,36,51,54,1,16,0,0,0,0,0,0,37,4,116,36,51,55,1,12,0,0,0,0,0,0,38,4,116,36,51,56,1,4,0,0,0,0,0,0,39,4,116,36,51,57,1,12,0,0,0,0,0,0]
theorem C77_4p0bound : C77_4p0.all wordBound = true := (by decide : [32,8,36,107,101,101,112,56,39,49,1,16,0,0,0,0,0,0,33,8,36,107,101,101,112,56,39,48,1,16,0,0,0,0,0,0,34,4,99,36,51,52,1,4,0,0,0,0,0,0,35,4,99,36,51,53,1,4,0,0,0,0,0,0,36,4,99,36,51,54,1,16,0,0,0,0,0,0,37,4,116,36,51,55,1,12,0,0,0,0,0,0,38,4,116,36,51,56,1,4,0,0,0,0,0,0,39,4,116,36,51,57,1,12,0,0,0,0,0,0].all wordBound = true)

def C77_4words : List Nat := C77_4p0

theorem C77_4wire : C77_4.flatMap columnWords = C77_4words := by
  rfl

theorem C77_4wordBound : C77_4words.all wordBound = true := by
  simp only [C77_4words,List.all_append,C77_4p0bound]
  try rfl

theorem C77_4bounded : ∀ n ∈ C77_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C77_4wordBound

theorem C77_4length : C77_4.length = 8 := by rfl

def C77_5 : List Column := [⟨40, [116,36,52,48], (some (4)), false, false, false⟩,⟨41, [116,36,52,49], (some (12)), false, false, false⟩,⟨42, [116,36,52,50], (some (4)), false, false, false⟩,⟨43, [36,114,101,116], (some (1)), false, false, false⟩]

def C77_5p0 : List Nat := [40,4,116,36,52,48,1,4,0,0,0,0,0,0,41,4,116,36,52,49,1,12,0,0,0,0,0,0,42,4,116,36,52,50,1,4,0,0,0,0,0,0,43,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C77_5p0bound : C77_5p0.all wordBound = true := (by decide : [40,4,116,36,52,48,1,4,0,0,0,0,0,0,41,4,116,36,52,49,1,12,0,0,0,0,0,0,42,4,116,36,52,50,1,4,0,0,0,0,0,0,43,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C77_5words : List Nat := C77_5p0

theorem C77_5wire : C77_5.flatMap columnWords = C77_5words := by
  rfl

theorem C77_5wordBound : C77_5words.all wordBound = true := by
  simp only [C77_5words,List.all_append,C77_5p0bound]
  try rfl

theorem C77_5bounded : ∀ n ∈ C77_5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C77_5wordBound

theorem C77_5length : C77_5.length = 4 := by rfl

def M77 : Module := ⟨77, [36,98,105,116,95,115,104,102,95,117,54,52,95,117,51], false, false, C77_0 ++ C77_1 ++ C77_2 ++ C77_3 ++ C77_4 ++ C77_5, ((List.range 0).map (fun n => [n]))⟩

def M77prefix : List Nat := [77,15,36,98,105,116,95,115,104,102,95,117,54,52,95,117,51,0,0,0,0,44]
theorem M77prefixwordBound : M77prefix.all wordBound = true := by decide

def M77words : List Nat := M77prefix ++ C77_0words ++ C77_1words ++ C77_2words ++ C77_3words ++ C77_4words ++ C77_5words ++ [0]

theorem M77wire : module.encode M77 = M77words := by
  rw [module_fast]
  simp only [M77,moduleWords,List.length_append,List.flatMap_append,C77_0length,C77_1length,C77_2length,C77_3length,C77_4length,C77_5length,C77_0wire,C77_1wire,C77_2wire,C77_3wire,C77_4wire,C77_5wire]
  rfl

theorem M77wordBound : M77words.all wordBound = true := by
  simp only [M77words,List.all_append,M77prefixwordBound,C77_0wordBound,C77_1wordBound,C77_2wordBound,C77_3wordBound,C77_4wordBound,C77_5wordBound]
  decide

theorem M77bounded : ∀ n ∈ M77words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M77wordBound

end DivRemFV.Replay
