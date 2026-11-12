import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C80_0 : List Column := [⟨0, [97,114,103,49,39,51], (some (16)), true, false, false⟩,⟨1, [97,114,103,49,39,50], (some (16)), true, false, false⟩,⟨2, [97,114,103,49,39,49], (some (16)), true, false, false⟩,⟨3, [97,114,103,49,39,48], (some (16)), true, false, false⟩,⟨4, [97,114,103,50], (some (6)), true, false, false⟩,⟨5, [111,117,116,95,115,104,108,39,51], (some (16)), false, true, false⟩,⟨6, [111,117,116,95,115,104,108,39,50], (some (16)), false, true, false⟩,⟨7, [111,117,116,95,115,104,108,39,49], (some (16)), false, true, false⟩]

def C80_0p0 : List Nat := [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,6,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1]
theorem C80_0p0bound : C80_0p0.all wordBound = true := (by decide : [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,6,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1].all wordBound = true)

def C80_0p1 : List Nat := [16,0,0,1,0,0,0]
theorem C80_0p1bound : C80_0p1.all wordBound = true := (by decide : [16,0,0,1,0,0,0].all wordBound = true)

def C80_0words : List Nat := C80_0p0 ++ C80_0p1

theorem C80_0wire : C80_0.flatMap columnWords = C80_0words := by
  rfl

theorem C80_0wordBound : C80_0words.all wordBound = true := by
  simp only [C80_0words,List.all_append,C80_0p0bound,C80_0p1bound]
  try rfl

theorem C80_0bounded : ∀ n ∈ C80_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C80_0wordBound

theorem C80_0length : C80_0.length = 8 := by rfl

def C80_1 : List Column := [⟨8, [111,117,116,95,115,104,108,39,48], (some (16)), false, true, false⟩,⟨9, [111,117,116,95,115,104,114,39,51], (some (16)), false, true, false⟩,⟨10, [111,117,116,95,115,104,114,39,50], (some (16)), false, true, false⟩,⟨11, [111,117,116,95,115,104,114,39,49], (some (16)), false, true, false⟩,⟨12, [111,117,116,95,115,104,114,39,48], (some (16)), false, true, false⟩,⟨13, [36,110,108,111,119,48], (some (5)), false, false, false⟩,⟨14, [36,98,105,116,49], (some (1)), false, false, false⟩,⟨15, [36,108,111,95,115,104,108,50,39,51], (some (16)), false, false, false⟩]

def C80_1p0 : List Nat := [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,110,108,111,119,48,1,5,0,0,0,0,0,0,14,5,36,98,105,116,49,1,1,0,0,0,0,0,0,15,10]
theorem C80_1p0bound : C80_1p0.all wordBound = true := (by decide : [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,110,108,111,119,48,1,5,0,0,0,0,0,0,14,5,36,98,105,116,49,1,1,0,0,0,0,0,0,15,10].all wordBound = true)

def C80_1p1 : List Nat := [36,108,111,95,115,104,108,50,39,51,1,16,0,0,0,0,0,0]
theorem C80_1p1bound : C80_1p1.all wordBound = true := (by decide : [36,108,111,95,115,104,108,50,39,51,1,16,0,0,0,0,0,0].all wordBound = true)

def C80_1words : List Nat := C80_1p0 ++ C80_1p1

theorem C80_1wire : C80_1.flatMap columnWords = C80_1words := by
  rfl

theorem C80_1wordBound : C80_1words.all wordBound = true := by
  simp only [C80_1words,List.all_append,C80_1p0bound,C80_1p1bound]
  try rfl

theorem C80_1bounded : ∀ n ∈ C80_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C80_1wordBound

theorem C80_1length : C80_1.length = 8 := by rfl

def C80_2 : List Column := [⟨16, [36,108,111,95,115,104,108,50,39,50], (some (16)), false, false, false⟩,⟨17, [36,108,111,95,115,104,108,50,39,49], (some (16)), false, false, false⟩,⟨18, [36,108,111,95,115,104,108,50,39,48], (some (16)), false, false, false⟩,⟨19, [36,108,111,95,115,104,114,51,39,51], (some (16)), false, false, false⟩,⟨20, [36,108,111,95,115,104,114,51,39,50], (some (16)), false, false, false⟩,⟨21, [36,108,111,95,115,104,114,51,39,49], (some (16)), false, false, false⟩,⟨22, [36,108,111,95,115,104,114,51,39,48], (some (16)), false, false, false⟩,⟨23, [36,100,114,111,112,52,39,49], (some (16)), false, false, false⟩]

def C80_2p0 : List Nat := [16,10,36,108,111,95,115,104,108,50,39,50,1,16,0,0,0,0,0,0,17,10,36,108,111,95,115,104,108,50,39,49,1,16,0,0,0,0,0,0,18,10,36,108,111,95,115,104,108,50,39,48,1,16,0,0,0,0,0,0,19,10,36,108,111,95,115,104,114,51,39,51,1,16,0,0,0,0,0,0,20,10,36,108,111,95,115,104,114,51,39,50,1,16,0,0,0,0,0,0,21,10,36,108,111,95,115,104,114,51,39,49,1,16,0,0,0,0,0,0,22,10,36,108,111,95,115,104]
theorem C80_2p0bound : C80_2p0.all wordBound = true := (by decide : [16,10,36,108,111,95,115,104,108,50,39,50,1,16,0,0,0,0,0,0,17,10,36,108,111,95,115,104,108,50,39,49,1,16,0,0,0,0,0,0,18,10,36,108,111,95,115,104,108,50,39,48,1,16,0,0,0,0,0,0,19,10,36,108,111,95,115,104,114,51,39,51,1,16,0,0,0,0,0,0,20,10,36,108,111,95,115,104,114,51,39,50,1,16,0,0,0,0,0,0,21,10,36,108,111,95,115,104,114,51,39,49,1,16,0,0,0,0,0,0,22,10,36,108,111,95,115,104].all wordBound = true)

def C80_2p1 : List Nat := [114,51,39,48,1,16,0,0,0,0,0,0,23,8,36,100,114,111,112,52,39,49,1,16,0,0,0,0,0,0]
theorem C80_2p1bound : C80_2p1.all wordBound = true := (by decide : [114,51,39,48,1,16,0,0,0,0,0,0,23,8,36,100,114,111,112,52,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C80_2words : List Nat := C80_2p0 ++ C80_2p1

theorem C80_2wire : C80_2.flatMap columnWords = C80_2words := by
  rfl

theorem C80_2wordBound : C80_2words.all wordBound = true := by
  simp only [C80_2words,List.all_append,C80_2p0bound,C80_2p1bound]
  try rfl

theorem C80_2bounded : ∀ n ∈ C80_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C80_2wordBound

theorem C80_2length : C80_2.length = 8 := by rfl

def C80_3 : List Column := [⟨24, [36,100,114,111,112,52,39,48], (some (16)), false, false, false⟩,⟨25, [36,107,101,101,112,53,39,49], (some (16)), false, false, false⟩,⟨26, [36,107,101,101,112,53,39,48], (some (16)), false, false, false⟩,⟨27, [36,122,101,114,111,115,54,39,49], (some (16)), false, false, false⟩,⟨28, [36,122,101,114,111,115,54,39,48], (some (16)), false, false, false⟩,⟨29, [36,100,114,111,112,55,39,49], (some (16)), false, false, false⟩,⟨30, [36,100,114,111,112,55,39,48], (some (16)), false, false, false⟩,⟨31, [36,107,101,101,112,56,39,49], (some (16)), false, false, false⟩]

def C80_3p0 : List Nat := [24,8,36,100,114,111,112,52,39,48,1,16,0,0,0,0,0,0,25,8,36,107,101,101,112,53,39,49,1,16,0,0,0,0,0,0,26,8,36,107,101,101,112,53,39,48,1,16,0,0,0,0,0,0,27,9,36,122,101,114,111,115,54,39,49,1,16,0,0,0,0,0,0,28,9,36,122,101,114,111,115,54,39,48,1,16,0,0,0,0,0,0,29,8,36,100,114,111,112,55,39,49,1,16,0,0,0,0,0,0,30,8,36,100,114,111,112,55,39,48,1,16,0,0,0,0,0,0]
theorem C80_3p0bound : C80_3p0.all wordBound = true := (by decide : [24,8,36,100,114,111,112,52,39,48,1,16,0,0,0,0,0,0,25,8,36,107,101,101,112,53,39,49,1,16,0,0,0,0,0,0,26,8,36,107,101,101,112,53,39,48,1,16,0,0,0,0,0,0,27,9,36,122,101,114,111,115,54,39,49,1,16,0,0,0,0,0,0,28,9,36,122,101,114,111,115,54,39,48,1,16,0,0,0,0,0,0,29,8,36,100,114,111,112,55,39,49,1,16,0,0,0,0,0,0,30,8,36,100,114,111,112,55,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C80_3p1 : List Nat := [31,8,36,107,101,101,112,56,39,49,1,16,0,0,0,0,0,0]
theorem C80_3p1bound : C80_3p1.all wordBound = true := (by decide : [31,8,36,107,101,101,112,56,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C80_3words : List Nat := C80_3p0 ++ C80_3p1

theorem C80_3wire : C80_3.flatMap columnWords = C80_3words := by
  rfl

theorem C80_3wordBound : C80_3words.all wordBound = true := by
  simp only [C80_3words,List.all_append,C80_3p0bound,C80_3p1bound]
  try rfl

theorem C80_3bounded : ∀ n ∈ C80_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C80_3wordBound

theorem C80_3length : C80_3.length = 8 := by rfl

def C80_4 : List Column := [⟨32, [36,107,101,101,112,56,39,48], (some (16)), false, false, false⟩,⟨33, [36,114,101,116], (some (1)), false, false, false⟩]

def C80_4p0 : List Nat := [32,8,36,107,101,101,112,56,39,48,1,16,0,0,0,0,0,0,33,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C80_4p0bound : C80_4p0.all wordBound = true := (by decide : [32,8,36,107,101,101,112,56,39,48,1,16,0,0,0,0,0,0,33,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C80_4words : List Nat := C80_4p0

theorem C80_4wire : C80_4.flatMap columnWords = C80_4words := by
  rfl

theorem C80_4wordBound : C80_4words.all wordBound = true := by
  simp only [C80_4words,List.all_append,C80_4p0bound]
  try rfl

theorem C80_4bounded : ∀ n ∈ C80_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C80_4wordBound

theorem C80_4length : C80_4.length = 2 := by rfl

def M80 : Module := ⟨80, [36,98,105,116,95,115,104,102,95,117,54,52,95,117,54], false, false, C80_0 ++ C80_1 ++ C80_2 ++ C80_3 ++ C80_4, ((List.range 0).map (fun n => [n]))⟩

def M80prefix : List Nat := [80,15,36,98,105,116,95,115,104,102,95,117,54,52,95,117,54,0,0,0,0,34]
theorem M80prefixwordBound : M80prefix.all wordBound = true := by decide

def M80words : List Nat := M80prefix ++ C80_0words ++ C80_1words ++ C80_2words ++ C80_3words ++ C80_4words ++ [0]

theorem M80wire : module.encode M80 = M80words := by
  rw [module_fast]
  simp only [M80,moduleWords,List.length_append,List.flatMap_append,C80_0length,C80_1length,C80_2length,C80_3length,C80_4length,C80_0wire,C80_1wire,C80_2wire,C80_3wire,C80_4wire]
  rfl

theorem M80wordBound : M80words.all wordBound = true := by
  simp only [M80words,List.all_append,M80prefixwordBound,C80_0wordBound,C80_1wordBound,C80_2wordBound,C80_3wordBound,C80_4wordBound]
  decide

theorem M80bounded : ∀ n ∈ M80words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M80wordBound

end DivRemFV.Replay
