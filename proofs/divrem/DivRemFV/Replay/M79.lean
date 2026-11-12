import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C79_0 : List Column := [⟨0, [97,114,103,49,39,51], (some (16)), true, false, false⟩,⟨1, [97,114,103,49,39,50], (some (16)), true, false, false⟩,⟨2, [97,114,103,49,39,49], (some (16)), true, false, false⟩,⟨3, [97,114,103,49,39,48], (some (16)), true, false, false⟩,⟨4, [97,114,103,50], (some (5)), true, false, false⟩,⟨5, [111,117,116,95,115,104,108,39,51], (some (16)), false, true, false⟩,⟨6, [111,117,116,95,115,104,108,39,50], (some (16)), false, true, false⟩,⟨7, [111,117,116,95,115,104,108,39,49], (some (16)), false, true, false⟩]

def C79_0p0 : List Nat := [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,5,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1]
theorem C79_0p0bound : C79_0p0.all wordBound = true := (by decide : [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,5,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1].all wordBound = true)

def C79_0p1 : List Nat := [16,0,0,1,0,0,0]
theorem C79_0p1bound : C79_0p1.all wordBound = true := (by decide : [16,0,0,1,0,0,0].all wordBound = true)

def C79_0words : List Nat := C79_0p0 ++ C79_0p1

theorem C79_0wire : C79_0.flatMap columnWords = C79_0words := by
  rfl

theorem C79_0wordBound : C79_0words.all wordBound = true := by
  simp only [C79_0words,List.all_append,C79_0p0bound,C79_0p1bound]
  try rfl

theorem C79_0bounded : ∀ n ∈ C79_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C79_0wordBound

theorem C79_0length : C79_0.length = 8 := by rfl

def C79_1 : List Column := [⟨8, [111,117,116,95,115,104,108,39,48], (some (16)), false, true, false⟩,⟨9, [111,117,116,95,115,104,114,39,51], (some (16)), false, true, false⟩,⟨10, [111,117,116,95,115,104,114,39,50], (some (16)), false, true, false⟩,⟨11, [111,117,116,95,115,104,114,39,49], (some (16)), false, true, false⟩,⟨12, [111,117,116,95,115,104,114,39,48], (some (16)), false, true, false⟩,⟨13, [36,110,108,111,119,48], (some (4)), false, false, false⟩,⟨14, [36,98,105,116,49], (some (1)), false, false, false⟩,⟨15, [36,108,111,95,115,104,108,50,39,51], (some (16)), false, false, false⟩]

def C79_1p0 : List Nat := [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,110,108,111,119,48,1,4,0,0,0,0,0,0,14,5,36,98,105,116,49,1,1,0,0,0,0,0,0,15,10]
theorem C79_1p0bound : C79_1p0.all wordBound = true := (by decide : [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,110,108,111,119,48,1,4,0,0,0,0,0,0,14,5,36,98,105,116,49,1,1,0,0,0,0,0,0,15,10].all wordBound = true)

def C79_1p1 : List Nat := [36,108,111,95,115,104,108,50,39,51,1,16,0,0,0,0,0,0]
theorem C79_1p1bound : C79_1p1.all wordBound = true := (by decide : [36,108,111,95,115,104,108,50,39,51,1,16,0,0,0,0,0,0].all wordBound = true)

def C79_1words : List Nat := C79_1p0 ++ C79_1p1

theorem C79_1wire : C79_1.flatMap columnWords = C79_1words := by
  rfl

theorem C79_1wordBound : C79_1words.all wordBound = true := by
  simp only [C79_1words,List.all_append,C79_1p0bound,C79_1p1bound]
  try rfl

theorem C79_1bounded : ∀ n ∈ C79_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C79_1wordBound

theorem C79_1length : C79_1.length = 8 := by rfl

def C79_2 : List Column := [⟨16, [36,108,111,95,115,104,108,50,39,50], (some (16)), false, false, false⟩,⟨17, [36,108,111,95,115,104,108,50,39,49], (some (16)), false, false, false⟩,⟨18, [36,108,111,95,115,104,108,50,39,48], (some (16)), false, false, false⟩,⟨19, [36,108,111,95,115,104,114,51,39,51], (some (16)), false, false, false⟩,⟨20, [36,108,111,95,115,104,114,51,39,50], (some (16)), false, false, false⟩,⟨21, [36,108,111,95,115,104,114,51,39,49], (some (16)), false, false, false⟩,⟨22, [36,108,111,95,115,104,114,51,39,48], (some (16)), false, false, false⟩,⟨23, [36,100,114,111,112,52], (some (16)), false, false, false⟩]

def C79_2p0 : List Nat := [16,10,36,108,111,95,115,104,108,50,39,50,1,16,0,0,0,0,0,0,17,10,36,108,111,95,115,104,108,50,39,49,1,16,0,0,0,0,0,0,18,10,36,108,111,95,115,104,108,50,39,48,1,16,0,0,0,0,0,0,19,10,36,108,111,95,115,104,114,51,39,51,1,16,0,0,0,0,0,0,20,10,36,108,111,95,115,104,114,51,39,50,1,16,0,0,0,0,0,0,21,10,36,108,111,95,115,104,114,51,39,49,1,16,0,0,0,0,0,0,22,10,36,108,111,95,115,104]
theorem C79_2p0bound : C79_2p0.all wordBound = true := (by decide : [16,10,36,108,111,95,115,104,108,50,39,50,1,16,0,0,0,0,0,0,17,10,36,108,111,95,115,104,108,50,39,49,1,16,0,0,0,0,0,0,18,10,36,108,111,95,115,104,108,50,39,48,1,16,0,0,0,0,0,0,19,10,36,108,111,95,115,104,114,51,39,51,1,16,0,0,0,0,0,0,20,10,36,108,111,95,115,104,114,51,39,50,1,16,0,0,0,0,0,0,21,10,36,108,111,95,115,104,114,51,39,49,1,16,0,0,0,0,0,0,22,10,36,108,111,95,115,104].all wordBound = true)

def C79_2p1 : List Nat := [114,51,39,48,1,16,0,0,0,0,0,0,23,6,36,100,114,111,112,52,1,16,0,0,0,0,0,0]
theorem C79_2p1bound : C79_2p1.all wordBound = true := (by decide : [114,51,39,48,1,16,0,0,0,0,0,0,23,6,36,100,114,111,112,52,1,16,0,0,0,0,0,0].all wordBound = true)

def C79_2words : List Nat := C79_2p0 ++ C79_2p1

theorem C79_2wire : C79_2.flatMap columnWords = C79_2words := by
  rfl

theorem C79_2wordBound : C79_2words.all wordBound = true := by
  simp only [C79_2words,List.all_append,C79_2p0bound,C79_2p1bound]
  try rfl

theorem C79_2bounded : ∀ n ∈ C79_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C79_2wordBound

theorem C79_2length : C79_2.length = 8 := by rfl

def C79_3 : List Column := [⟨24, [36,107,101,101,112,53,39,50], (some (16)), false, false, false⟩,⟨25, [36,107,101,101,112,53,39,49], (some (16)), false, false, false⟩,⟨26, [36,107,101,101,112,53,39,48], (some (16)), false, false, false⟩,⟨27, [36,122,101,114,111,115,54], (some (16)), false, false, false⟩,⟨28, [36,100,114,111,112,55], (some (16)), false, false, false⟩,⟨29, [36,107,101,101,112,56,39,50], (some (16)), false, false, false⟩,⟨30, [36,107,101,101,112,56,39,49], (some (16)), false, false, false⟩,⟨31, [36,107,101,101,112,56,39,48], (some (16)), false, false, false⟩]

def C79_3p0 : List Nat := [24,8,36,107,101,101,112,53,39,50,1,16,0,0,0,0,0,0,25,8,36,107,101,101,112,53,39,49,1,16,0,0,0,0,0,0,26,8,36,107,101,101,112,53,39,48,1,16,0,0,0,0,0,0,27,7,36,122,101,114,111,115,54,1,16,0,0,0,0,0,0,28,6,36,100,114,111,112,55,1,16,0,0,0,0,0,0,29,8,36,107,101,101,112,56,39,50,1,16,0,0,0,0,0,0,30,8,36,107,101,101,112,56,39,49,1,16,0,0,0,0,0,0,31,8,36,107,101]
theorem C79_3p0bound : C79_3p0.all wordBound = true := (by decide : [24,8,36,107,101,101,112,53,39,50,1,16,0,0,0,0,0,0,25,8,36,107,101,101,112,53,39,49,1,16,0,0,0,0,0,0,26,8,36,107,101,101,112,53,39,48,1,16,0,0,0,0,0,0,27,7,36,122,101,114,111,115,54,1,16,0,0,0,0,0,0,28,6,36,100,114,111,112,55,1,16,0,0,0,0,0,0,29,8,36,107,101,101,112,56,39,50,1,16,0,0,0,0,0,0,30,8,36,107,101,101,112,56,39,49,1,16,0,0,0,0,0,0,31,8,36,107,101].all wordBound = true)

def C79_3p1 : List Nat := [101,112,56,39,48,1,16,0,0,0,0,0,0]
theorem C79_3p1bound : C79_3p1.all wordBound = true := (by decide : [101,112,56,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C79_3words : List Nat := C79_3p0 ++ C79_3p1

theorem C79_3wire : C79_3.flatMap columnWords = C79_3words := by
  rfl

theorem C79_3wordBound : C79_3words.all wordBound = true := by
  simp only [C79_3words,List.all_append,C79_3p0bound,C79_3p1bound]
  try rfl

theorem C79_3bounded : ∀ n ∈ C79_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C79_3wordBound

theorem C79_3length : C79_3.length = 8 := by rfl

def C79_4 : List Column := [⟨32, [36,114,101,116], (some (1)), false, false, false⟩]

def C79_4p0 : List Nat := [32,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C79_4p0bound : C79_4p0.all wordBound = true := (by decide : [32,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C79_4words : List Nat := C79_4p0

theorem C79_4wire : C79_4.flatMap columnWords = C79_4words := by
  rfl

theorem C79_4wordBound : C79_4words.all wordBound = true := by
  simp only [C79_4words,List.all_append,C79_4p0bound]
  try rfl

theorem C79_4bounded : ∀ n ∈ C79_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C79_4wordBound

theorem C79_4length : C79_4.length = 1 := by rfl

def M79 : Module := ⟨79, [36,98,105,116,95,115,104,102,95,117,54,52,95,117,53], false, false, C79_0 ++ C79_1 ++ C79_2 ++ C79_3 ++ C79_4, ((List.range 0).map (fun n => [n]))⟩

def M79prefix : List Nat := [79,15,36,98,105,116,95,115,104,102,95,117,54,52,95,117,53,0,0,0,0,33]
theorem M79prefixwordBound : M79prefix.all wordBound = true := by decide

def M79words : List Nat := M79prefix ++ C79_0words ++ C79_1words ++ C79_2words ++ C79_3words ++ C79_4words ++ [0]

theorem M79wire : module.encode M79 = M79words := by
  rw [module_fast]
  simp only [M79,moduleWords,List.length_append,List.flatMap_append,C79_0length,C79_1length,C79_2length,C79_3length,C79_4length,C79_0wire,C79_1wire,C79_2wire,C79_3wire,C79_4wire]
  rfl

theorem M79wordBound : M79words.all wordBound = true := by
  simp only [M79words,List.all_append,M79prefixwordBound,C79_0wordBound,C79_1wordBound,C79_2wordBound,C79_3wordBound,C79_4wordBound]
  decide

theorem M79bounded : ∀ n ∈ M79words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M79wordBound

end DivRemFV.Replay
