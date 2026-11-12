import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C75_0 : List Column := [⟨0, [97,114,103,49,39,51], (some (16)), true, false, false⟩,⟨1, [97,114,103,49,39,50], (some (16)), true, false, false⟩,⟨2, [97,114,103,49,39,49], (some (16)), true, false, false⟩,⟨3, [97,114,103,49,39,48], (some (16)), true, false, false⟩,⟨4, [97,114,103,50], (some (1)), true, false, false⟩,⟨5, [111,117,116,95,115,104,108,39,51], (some (16)), false, true, false⟩,⟨6, [111,117,116,95,115,104,108,39,50], (some (16)), false, true, false⟩,⟨7, [111,117,116,95,115,104,108,39,49], (some (16)), false, true, false⟩]

def C75_0p0 : List Nat := [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,1,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1]
theorem C75_0p0bound : C75_0p0.all wordBound = true := (by decide : [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,1,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1].all wordBound = true)

def C75_0p1 : List Nat := [16,0,0,1,0,0,0]
theorem C75_0p1bound : C75_0p1.all wordBound = true := (by decide : [16,0,0,1,0,0,0].all wordBound = true)

def C75_0words : List Nat := C75_0p0 ++ C75_0p1

theorem C75_0wire : C75_0.flatMap columnWords = C75_0words := by
  rfl

theorem C75_0wordBound : C75_0words.all wordBound = true := by
  simp only [C75_0words,List.all_append,C75_0p0bound,C75_0p1bound]
  try rfl

theorem C75_0bounded : ∀ n ∈ C75_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C75_0wordBound

theorem C75_0length : C75_0.length = 8 := by rfl

def C75_1 : List Column := [⟨8, [111,117,116,95,115,104,108,39,48], (some (16)), false, true, false⟩,⟨9, [111,117,116,95,115,104,114,39,51], (some (16)), false, true, false⟩,⟨10, [111,117,116,95,115,104,114,39,50], (some (16)), false, true, false⟩,⟨11, [111,117,116,95,115,104,114,39,49], (some (16)), false, true, false⟩,⟨12, [111,117,116,95,115,104,114,39,48], (some (16)), false, true, false⟩,⟨13, [36,100,114,111,112,48], (some (1)), false, false, false⟩,⟨14, [36,107,101,101,112,49,39,51], (some (15)), false, false, false⟩,⟨15, [36,107,101,101,112,49,39,50], (some (16)), false, false, false⟩]

def C75_1p0 : List Nat := [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,100,114,111,112,48,1,1,0,0,0,0,0,0,14,8,36,107,101,101,112,49,39,51,1,15,0,0,0,0,0]
theorem C75_1p0bound : C75_1p0.all wordBound = true := (by decide : [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,100,114,111,112,48,1,1,0,0,0,0,0,0,14,8,36,107,101,101,112,49,39,51,1,15,0,0,0,0,0].all wordBound = true)

def C75_1p1 : List Nat := [0,15,8,36,107,101,101,112,49,39,50,1,16,0,0,0,0,0,0]
theorem C75_1p1bound : C75_1p1.all wordBound = true := (by decide : [0,15,8,36,107,101,101,112,49,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C75_1words : List Nat := C75_1p0 ++ C75_1p1

theorem C75_1wire : C75_1.flatMap columnWords = C75_1words := by
  rfl

theorem C75_1wordBound : C75_1words.all wordBound = true := by
  simp only [C75_1words,List.all_append,C75_1p0bound,C75_1p1bound]
  try rfl

theorem C75_1bounded : ∀ n ∈ C75_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C75_1wordBound

theorem C75_1length : C75_1.length = 8 := by rfl

def C75_2 : List Column := [⟨16, [36,107,101,101,112,49,39,49], (some (16)), false, false, false⟩,⟨17, [36,107,101,101,112,49,39,48], (some (16)), false, false, false⟩,⟨18, [36,122,101,114,111,115,50], (some (1)), false, false, false⟩,⟨19, [36,100,114,111,112,51], (some (1)), false, false, false⟩,⟨20, [36,107,101,101,112,52,39,51], (some (15)), false, false, false⟩,⟨21, [36,107,101,101,112,52,39,50], (some (16)), false, false, false⟩,⟨22, [36,107,101,101,112,52,39,49], (some (16)), false, false, false⟩,⟨23, [36,107,101,101,112,52,39,48], (some (16)), false, false, false⟩]

def C75_2p0 : List Nat := [16,8,36,107,101,101,112,49,39,49,1,16,0,0,0,0,0,0,17,8,36,107,101,101,112,49,39,48,1,16,0,0,0,0,0,0,18,7,36,122,101,114,111,115,50,1,1,0,0,0,0,0,0,19,6,36,100,114,111,112,51,1,1,0,0,0,0,0,0,20,8,36,107,101,101,112,52,39,51,1,15,0,0,0,0,0,0,21,8,36,107,101,101,112,52,39,50,1,16,0,0,0,0,0,0,22,8,36,107,101,101,112,52,39,49,1,16,0,0,0,0,0,0,23,8,36,107,101]
theorem C75_2p0bound : C75_2p0.all wordBound = true := (by decide : [16,8,36,107,101,101,112,49,39,49,1,16,0,0,0,0,0,0,17,8,36,107,101,101,112,49,39,48,1,16,0,0,0,0,0,0,18,7,36,122,101,114,111,115,50,1,1,0,0,0,0,0,0,19,6,36,100,114,111,112,51,1,1,0,0,0,0,0,0,20,8,36,107,101,101,112,52,39,51,1,15,0,0,0,0,0,0,21,8,36,107,101,101,112,52,39,50,1,16,0,0,0,0,0,0,22,8,36,107,101,101,112,52,39,49,1,16,0,0,0,0,0,0,23,8,36,107,101].all wordBound = true)

def C75_2p1 : List Nat := [101,112,52,39,48,1,16,0,0,0,0,0,0]
theorem C75_2p1bound : C75_2p1.all wordBound = true := (by decide : [101,112,52,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C75_2words : List Nat := C75_2p0 ++ C75_2p1

theorem C75_2wire : C75_2.flatMap columnWords = C75_2words := by
  rfl

theorem C75_2wordBound : C75_2words.all wordBound = true := by
  simp only [C75_2words,List.all_append,C75_2p0bound,C75_2p1bound]
  try rfl

theorem C75_2bounded : ∀ n ∈ C75_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C75_2wordBound

theorem C75_2length : C75_2.length = 8 := by rfl

def C75_3 : List Column := [⟨24, [99,36,50,52], (some (1)), false, false, false⟩,⟨25, [99,36,50,53], (some (1)), false, false, false⟩,⟨26, [99,36,50,54], (some (1)), false, false, false⟩,⟨27, [116,36,50,55], (some (15)), false, false, false⟩,⟨28, [116,36,50,56], (some (1)), false, false, false⟩,⟨29, [116,36,50,57], (some (15)), false, false, false⟩,⟨30, [116,36,51,48], (some (1)), false, false, false⟩,⟨31, [116,36,51,49], (some (15)), false, false, false⟩]

def C75_3p0 : List Nat := [24,4,99,36,50,52,1,1,0,0,0,0,0,0,25,4,99,36,50,53,1,1,0,0,0,0,0,0,26,4,99,36,50,54,1,1,0,0,0,0,0,0,27,4,116,36,50,55,1,15,0,0,0,0,0,0,28,4,116,36,50,56,1,1,0,0,0,0,0,0,29,4,116,36,50,57,1,15,0,0,0,0,0,0,30,4,116,36,51,48,1,1,0,0,0,0,0,0,31,4,116,36,51,49,1,15,0,0,0,0,0,0]
theorem C75_3p0bound : C75_3p0.all wordBound = true := (by decide : [24,4,99,36,50,52,1,1,0,0,0,0,0,0,25,4,99,36,50,53,1,1,0,0,0,0,0,0,26,4,99,36,50,54,1,1,0,0,0,0,0,0,27,4,116,36,50,55,1,15,0,0,0,0,0,0,28,4,116,36,50,56,1,1,0,0,0,0,0,0,29,4,116,36,50,57,1,15,0,0,0,0,0,0,30,4,116,36,51,48,1,1,0,0,0,0,0,0,31,4,116,36,51,49,1,15,0,0,0,0,0,0].all wordBound = true)

def C75_3words : List Nat := C75_3p0

theorem C75_3wire : C75_3.flatMap columnWords = C75_3words := by
  rfl

theorem C75_3wordBound : C75_3words.all wordBound = true := by
  simp only [C75_3words,List.all_append,C75_3p0bound]
  try rfl

theorem C75_3bounded : ∀ n ∈ C75_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C75_3wordBound

theorem C75_3length : C75_3.length = 8 := by rfl

def C75_4 : List Column := [⟨32, [116,36,51,50], (some (1)), false, false, false⟩,⟨33, [36,114,101,116], (some (1)), false, false, false⟩]

def C75_4p0 : List Nat := [32,4,116,36,51,50,1,1,0,0,0,0,0,0,33,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C75_4p0bound : C75_4p0.all wordBound = true := (by decide : [32,4,116,36,51,50,1,1,0,0,0,0,0,0,33,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C75_4words : List Nat := C75_4p0

theorem C75_4wire : C75_4.flatMap columnWords = C75_4words := by
  rfl

theorem C75_4wordBound : C75_4words.all wordBound = true := by
  simp only [C75_4words,List.all_append,C75_4p0bound]
  try rfl

theorem C75_4bounded : ∀ n ∈ C75_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C75_4wordBound

theorem C75_4length : C75_4.length = 2 := by rfl

def M75 : Module := ⟨75, [36,98,105,116,95,115,104,102,95,117,54,52,95,117,49], false, false, C75_0 ++ C75_1 ++ C75_2 ++ C75_3 ++ C75_4, ((List.range 0).map (fun n => [n]))⟩

def M75prefix : List Nat := [75,15,36,98,105,116,95,115,104,102,95,117,54,52,95,117,49,0,0,0,0,34]
theorem M75prefixwordBound : M75prefix.all wordBound = true := by decide

def M75words : List Nat := M75prefix ++ C75_0words ++ C75_1words ++ C75_2words ++ C75_3words ++ C75_4words ++ [0]

theorem M75wire : module.encode M75 = M75words := by
  rw [module_fast]
  simp only [M75,moduleWords,List.length_append,List.flatMap_append,C75_0length,C75_1length,C75_2length,C75_3length,C75_4length,C75_0wire,C75_1wire,C75_2wire,C75_3wire,C75_4wire]
  rfl

theorem M75wordBound : M75words.all wordBound = true := by
  simp only [M75words,List.all_append,M75prefixwordBound,C75_0wordBound,C75_1wordBound,C75_2wordBound,C75_3wordBound,C75_4wordBound]
  decide

theorem M75bounded : ∀ n ∈ M75words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M75wordBound

end DivRemFV.Replay
