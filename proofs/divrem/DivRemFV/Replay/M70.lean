import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C70_0 : List Column := [⟨0, [118,97,108,117,101,39,51], (some (16)), true, false, false⟩,⟨1, [118,97,108,117,101,39,50], (some (16)), true, false, false⟩,⟨2, [118,97,108,117,101,39,49], (some (16)), true, false, false⟩,⟨3, [118,97,108,117,101,39,48], (some (16)), true, false, false⟩,⟨4, [115,104,97,109,116], (some (6)), true, false, false⟩,⟨5, [111,117,116,39,51], (some (16)), false, true, false⟩,⟨6, [111,117,116,39,50], (some (16)), false, true, false⟩,⟨7, [111,117,116,39,49], (some (16)), false, true, false⟩]

def C70_0p0 : List Nat := [0,7,118,97,108,117,101,39,51,1,16,1,0,0,0,0,0,1,7,118,97,108,117,101,39,50,1,16,1,0,0,0,0,0,2,7,118,97,108,117,101,39,49,1,16,1,0,0,0,0,0,3,7,118,97,108,117,101,39,48,1,16,1,0,0,0,0,0,4,5,115,104,97,109,116,1,6,1,0,0,0,0,0,5,5,111,117,116,39,51,1,16,0,0,1,0,0,0,6,5,111,117,116,39,50,1,16,0,0,1,0,0,0,7,5,111,117,116,39,49,1,16,0,0,1,0,0,0]
theorem C70_0p0bound : C70_0p0.all wordBound = true := (by decide : [0,7,118,97,108,117,101,39,51,1,16,1,0,0,0,0,0,1,7,118,97,108,117,101,39,50,1,16,1,0,0,0,0,0,2,7,118,97,108,117,101,39,49,1,16,1,0,0,0,0,0,3,7,118,97,108,117,101,39,48,1,16,1,0,0,0,0,0,4,5,115,104,97,109,116,1,6,1,0,0,0,0,0,5,5,111,117,116,39,51,1,16,0,0,1,0,0,0,6,5,111,117,116,39,50,1,16,0,0,1,0,0,0,7,5,111,117,116,39,49,1,16,0,0,1,0,0,0].all wordBound = true)

def C70_0words : List Nat := C70_0p0

theorem C70_0wire : C70_0.flatMap columnWords = C70_0words := by
  rfl

theorem C70_0wordBound : C70_0words.all wordBound = true := by
  simp only [C70_0words,List.all_append,C70_0p0bound]
  try rfl

theorem C70_0bounded : ∀ n ∈ C70_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C70_0wordBound

theorem C70_0length : C70_0.length = 8 := by rfl

def C70_1 : List Column := [⟨8, [111,117,116,39,48], (some (16)), false, true, false⟩,⟨9, [115,105,103,110], (some (1)), false, false, false⟩,⟨10, [108,111,103,105,99,97,108,39,51], (some (16)), false, false, false⟩,⟨11, [108,111,103,105,99,97,108,39,50], (some (16)), false, false, false⟩,⟨12, [108,111,103,105,99,97,108,39,49], (some (16)), false, false, false⟩,⟨13, [108,111,103,105,99,97,108,39,48], (some (16)), false, false, false⟩,⟨14, [109,97,115,107,39,51], (some (16)), false, false, false⟩,⟨15, [109,97,115,107,39,50], (some (16)), false, false, false⟩]

def C70_1p0 : List Nat := [8,5,111,117,116,39,48,1,16,0,0,1,0,0,0,9,4,115,105,103,110,1,1,0,0,0,0,0,0,10,9,108,111,103,105,99,97,108,39,51,1,16,0,0,0,0,0,0,11,9,108,111,103,105,99,97,108,39,50,1,16,0,0,0,0,0,0,12,9,108,111,103,105,99,97,108,39,49,1,16,0,0,0,0,0,0,13,9,108,111,103,105,99,97,108,39,48,1,16,0,0,0,0,0,0,14,6,109,97,115,107,39,51,1,16,0,0,0,0,0,0,15,6,109,97,115,107,39]
theorem C70_1p0bound : C70_1p0.all wordBound = true := (by decide : [8,5,111,117,116,39,48,1,16,0,0,1,0,0,0,9,4,115,105,103,110,1,1,0,0,0,0,0,0,10,9,108,111,103,105,99,97,108,39,51,1,16,0,0,0,0,0,0,11,9,108,111,103,105,99,97,108,39,50,1,16,0,0,0,0,0,0,12,9,108,111,103,105,99,97,108,39,49,1,16,0,0,0,0,0,0,13,9,108,111,103,105,99,97,108,39,48,1,16,0,0,0,0,0,0,14,6,109,97,115,107,39,51,1,16,0,0,0,0,0,0,15,6,109,97,115,107,39].all wordBound = true)

def C70_1p1 : List Nat := [50,1,16,0,0,0,0,0,0]
theorem C70_1p1bound : C70_1p1.all wordBound = true := (by decide : [50,1,16,0,0,0,0,0,0].all wordBound = true)

def C70_1words : List Nat := C70_1p0 ++ C70_1p1

theorem C70_1wire : C70_1.flatMap columnWords = C70_1words := by
  rfl

theorem C70_1wordBound : C70_1words.all wordBound = true := by
  simp only [C70_1words,List.all_append,C70_1p0bound,C70_1p1bound]
  try rfl

theorem C70_1bounded : ∀ n ∈ C70_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C70_1wordBound

theorem C70_1length : C70_1.length = 8 := by rfl

def C70_2 : List Column := [⟨16, [109,97,115,107,39,49], (some (16)), false, false, false⟩,⟨17, [109,97,115,107,39,48], (some (16)), false, false, false⟩,⟨18, [36,54,39,51], (some (16)), false, false, false⟩,⟨19, [36,54,39,50], (some (16)), false, false, false⟩,⟨20, [36,54,39,49], (some (16)), false, false, false⟩,⟨21, [36,54,39,48], (some (16)), false, false, false⟩,⟨22, [36,55,39,51], (some (16)), false, false, false⟩,⟨23, [36,55,39,50], (some (16)), false, false, false⟩]

def C70_2p0 : List Nat := [16,6,109,97,115,107,39,49,1,16,0,0,0,0,0,0,17,6,109,97,115,107,39,48,1,16,0,0,0,0,0,0,18,4,36,54,39,51,1,16,0,0,0,0,0,0,19,4,36,54,39,50,1,16,0,0,0,0,0,0,20,4,36,54,39,49,1,16,0,0,0,0,0,0,21,4,36,54,39,48,1,16,0,0,0,0,0,0,22,4,36,55,39,51,1,16,0,0,0,0,0,0,23,4,36,55,39,50,1,16,0,0,0,0,0,0]
theorem C70_2p0bound : C70_2p0.all wordBound = true := (by decide : [16,6,109,97,115,107,39,49,1,16,0,0,0,0,0,0,17,6,109,97,115,107,39,48,1,16,0,0,0,0,0,0,18,4,36,54,39,51,1,16,0,0,0,0,0,0,19,4,36,54,39,50,1,16,0,0,0,0,0,0,20,4,36,54,39,49,1,16,0,0,0,0,0,0,21,4,36,54,39,48,1,16,0,0,0,0,0,0,22,4,36,55,39,51,1,16,0,0,0,0,0,0,23,4,36,55,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C70_2words : List Nat := C70_2p0

theorem C70_2wire : C70_2.flatMap columnWords = C70_2words := by
  rfl

theorem C70_2wordBound : C70_2words.all wordBound = true := by
  simp only [C70_2words,List.all_append,C70_2p0bound]
  try rfl

theorem C70_2bounded : ∀ n ∈ C70_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C70_2wordBound

theorem C70_2length : C70_2.length = 8 := by rfl

def C70_3 : List Column := [⟨24, [36,55,39,49], (some (16)), false, false, false⟩,⟨25, [36,55,39,48], (some (16)), false, false, false⟩,⟨26, [115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,51], (some (15)), false, false, false⟩,⟨27, [115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,50], (some (16)), false, false, false⟩,⟨28, [115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,49], (some (16)), false, false, false⟩,⟨29, [115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,48], (some (16)), false, false, false⟩,⟨30, [108,98,119,36,57,39,51], (some (16)), false, false, false⟩,⟨31, [108,98,119,36,57,39,50], (some (16)), false, false, false⟩]

def C70_3p0 : List Nat := [24,4,36,55,39,49,1,16,0,0,0,0,0,0,25,4,36,55,39,48,1,16,0,0,0,0,0,0,26,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,51,1,15,0,0,0,0,0,0,27,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,50,1,16,0,0,0,0,0,0,28,36,115,105,103,110,95,98]
theorem C70_3p0bound : C70_3p0.all wordBound = true := (by decide : [24,4,36,55,39,49,1,16,0,0,0,0,0,0,25,4,36,55,39,48,1,16,0,0,0,0,0,0,26,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,51,1,15,0,0,0,0,0,0,27,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,50,1,16,0,0,0,0,0,0,28,36,115,105,103,110,95,98].all wordBound = true)

def C70_3p1 : List Nat := [105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,49,1,16,0,0,0,0,0,0,29,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,48,1,16,0,0,0,0,0,0,30,7,108,98,119,36,57,39,51,1,16,0,0,0,0,0,0,31,7,108,98,119,36,57,39,50,1,16,0,0,0,0,0,0]
theorem C70_3p1bound : C70_3p1.all wordBound = true := (by decide : [105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,49,1,16,0,0,0,0,0,0,29,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,56,39,48,1,16,0,0,0,0,0,0,30,7,108,98,119,36,57,39,51,1,16,0,0,0,0,0,0,31,7,108,98,119,36,57,39,50,1,16,0,0,0,0,0,0].all wordBound = true)

def C70_3words : List Nat := C70_3p0 ++ C70_3p1

theorem C70_3wire : C70_3.flatMap columnWords = C70_3words := by
  rfl

theorem C70_3wordBound : C70_3words.all wordBound = true := by
  simp only [C70_3words,List.all_append,C70_3p0bound,C70_3p1bound]
  try rfl

theorem C70_3bounded : ∀ n ∈ C70_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C70_3wordBound

theorem C70_3length : C70_3.length = 8 := by rfl

def C70_4 : List Column := [⟨32, [108,98,119,36,57,39,49], (some (16)), false, false, false⟩,⟨33, [108,98,119,36,57,39,48], (some (16)), false, false, false⟩,⟨34, [98,36,51,52], (some (1)), false, false, false⟩,⟨35, [98,36,51,53], (some (1)), false, false, false⟩,⟨36, [98,36,51,54], (some (1)), false, false, false⟩,⟨37, [36,114,101,116], (some (1)), false, false, false⟩,⟨38, [36,108,111,111,107,117,112,95,115,101,108,95,51,56], (some (1)), false, false, false⟩]

def C70_4p0 : List Nat := [32,7,108,98,119,36,57,39,49,1,16,0,0,0,0,0,0,33,7,108,98,119,36,57,39,48,1,16,0,0,0,0,0,0,34,4,98,36,51,52,1,1,0,0,0,0,0,0,35,4,98,36,51,53,1,1,0,0,0,0,0,0,36,4,98,36,51,54,1,1,0,0,0,0,0,0,37,4,36,114,101,116,1,1,0,0,0,0,0,0,38,14,36,108,111,111,107,117,112,95,115,101,108,95,51,56,1,1,0,0,0,0,0,0]
theorem C70_4p0bound : C70_4p0.all wordBound = true := (by decide : [32,7,108,98,119,36,57,39,49,1,16,0,0,0,0,0,0,33,7,108,98,119,36,57,39,48,1,16,0,0,0,0,0,0,34,4,98,36,51,52,1,1,0,0,0,0,0,0,35,4,98,36,51,53,1,1,0,0,0,0,0,0,36,4,98,36,51,54,1,1,0,0,0,0,0,0,37,4,36,114,101,116,1,1,0,0,0,0,0,0,38,14,36,108,111,111,107,117,112,95,115,101,108,95,51,56,1,1,0,0,0,0,0,0].all wordBound = true)

def C70_4words : List Nat := C70_4p0

theorem C70_4wire : C70_4.flatMap columnWords = C70_4words := by
  rfl

theorem C70_4wordBound : C70_4words.all wordBound = true := by
  simp only [C70_4words,List.all_append,C70_4p0bound]
  try rfl

theorem C70_4bounded : ∀ n ∈ C70_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C70_4wordBound

theorem C70_4length : C70_4.length = 7 := by rfl

def M70 : Module := ⟨70, [95,97,115,104,114,95,117,54,52], false, false, C70_0 ++ C70_1 ++ C70_2 ++ C70_3 ++ C70_4, ((List.range 0).map (fun n => [n]))⟩

def M70prefix : List Nat := [70,9,95,97,115,104,114,95,117,54,52,0,0,0,0,39]
theorem M70prefixwordBound : M70prefix.all wordBound = true := by decide

def M70words : List Nat := M70prefix ++ C70_0words ++ C70_1words ++ C70_2words ++ C70_3words ++ C70_4words ++ [0]

theorem M70wire : module.encode M70 = M70words := by
  rw [module_fast]
  simp only [M70,moduleWords,List.length_append,List.flatMap_append,C70_0length,C70_1length,C70_2length,C70_3length,C70_4length,C70_0wire,C70_1wire,C70_2wire,C70_3wire,C70_4wire]
  rfl

theorem M70wordBound : M70words.all wordBound = true := by
  simp only [M70words,List.all_append,M70prefixwordBound,C70_0wordBound,C70_1wordBound,C70_2wordBound,C70_3wordBound,C70_4wordBound]
  decide

theorem M70bounded : ∀ n ∈ M70words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M70wordBound

end DivRemFV.Replay
