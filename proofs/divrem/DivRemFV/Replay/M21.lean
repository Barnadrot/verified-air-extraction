import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C21_0 : List Column := [⟨0, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,51], (some (16)), true, false, false⟩,⟨3, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,50], (some (16)), true, false, false⟩,⟨4, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,49], (some (16)), true, false, false⟩,⟨5, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,48], (some (16)), true, false, false⟩,⟨6, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨7, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩]

def C21_0p0 : List Nat := [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,51,1,16,1,0,0,0,0,0,3,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,50,1,16,1,0,0,0,0,0,4,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116]
theorem C21_0p0bound : C21_0p0.all wordBound = true := (by decide : [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,51,1,16,1,0,0,0,0,0,3,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,50,1,16,1,0,0,0,0,0,4,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116].all wordBound = true)

def C21_0p1 : List Nat := [39,49,1,16,1,0,0,0,0,0,5,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,48,1,16,1,0,0,0,0,0,6,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,7,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0]
theorem C21_0p1bound : C21_0p1.all wordBound = true := (by decide : [39,49,1,16,1,0,0,0,0,0,5,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,48,1,16,1,0,0,0,0,0,6,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,7,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C21_0words : List Nat := C21_0p0 ++ C21_0p1

theorem C21_0wire : C21_0.flatMap columnWords = C21_0words := by
  rfl

theorem C21_0wordBound : C21_0words.all wordBound = true := by
  simp only [C21_0words,List.all_append,C21_0p0bound,C21_0p1bound]
  try rfl

theorem C21_0bounded : ∀ n ∈ C21_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C21_0wordBound

theorem C21_0length : C21_0.length = 8 := by rfl

def C21_1 : List Column := [⟨8, [36,49], (some (7)), false, false, false⟩,⟨9, [36,50,39,51], (some (16)), false, false, false⟩,⟨10, [36,50,39,50], (some (16)), false, false, false⟩,⟨11, [36,50,39,49], (some (16)), false, false, false⟩,⟨12, [36,50,39,48], (some (16)), false, false, false⟩,⟨13, [36,51,39,51], (some (16)), false, false, false⟩,⟨14, [36,51,39,50], (some (16)), false, false, false⟩,⟨15, [36,51,39,49], (some (16)), false, false, false⟩]

def C21_1p0 : List Nat := [8,2,36,49,1,7,0,0,0,0,0,0,9,4,36,50,39,51,1,16,0,0,0,0,0,0,10,4,36,50,39,50,1,16,0,0,0,0,0,0,11,4,36,50,39,49,1,16,0,0,0,0,0,0,12,4,36,50,39,48,1,16,0,0,0,0,0,0,13,4,36,51,39,51,1,16,0,0,0,0,0,0,14,4,36,51,39,50,1,16,0,0,0,0,0,0,15,4,36,51,39,49,1,16,0,0,0,0,0,0]
theorem C21_1p0bound : C21_1p0.all wordBound = true := (by decide : [8,2,36,49,1,7,0,0,0,0,0,0,9,4,36,50,39,51,1,16,0,0,0,0,0,0,10,4,36,50,39,50,1,16,0,0,0,0,0,0,11,4,36,50,39,49,1,16,0,0,0,0,0,0,12,4,36,50,39,48,1,16,0,0,0,0,0,0,13,4,36,51,39,51,1,16,0,0,0,0,0,0,14,4,36,51,39,50,1,16,0,0,0,0,0,0,15,4,36,51,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C21_1words : List Nat := C21_1p0

theorem C21_1wire : C21_1.flatMap columnWords = C21_1words := by
  rfl

theorem C21_1wordBound : C21_1words.all wordBound = true := by
  simp only [C21_1words,List.all_append,C21_1p0bound]
  try rfl

theorem C21_1bounded : ∀ n ∈ C21_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C21_1wordBound

theorem C21_1length : C21_1.length = 8 := by rfl

def C21_2 : List Column := [⟨16, [36,51,39,48], (some (16)), false, false, false⟩,⟨17, [36,52], (some (7)), false, false, false⟩,⟨18, [115,116,97,109,112,36,55,39,49], (some (16)), false, false, false⟩,⟨19, [115,116,97,109,112,36,55,39,48], (some (16)), false, false, false⟩,⟨20, [99,36,50,48], (some (1)), false, false, false⟩,⟨21, [99,36,50,49], (some (1)), false, false, false⟩,⟨22, [36,114,101,116], (some (1)), false, false, false⟩]

def C21_2p0 : List Nat := [16,4,36,51,39,48,1,16,0,0,0,0,0,0,17,2,36,52,1,7,0,0,0,0,0,0,18,9,115,116,97,109,112,36,55,39,49,1,16,0,0,0,0,0,0,19,9,115,116,97,109,112,36,55,39,48,1,16,0,0,0,0,0,0,20,4,99,36,50,48,1,1,0,0,0,0,0,0,21,4,99,36,50,49,1,1,0,0,0,0,0,0,22,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C21_2p0bound : C21_2p0.all wordBound = true := (by decide : [16,4,36,51,39,48,1,16,0,0,0,0,0,0,17,2,36,52,1,7,0,0,0,0,0,0,18,9,115,116,97,109,112,36,55,39,49,1,16,0,0,0,0,0,0,19,9,115,116,97,109,112,36,55,39,48,1,16,0,0,0,0,0,0,20,4,99,36,50,48,1,1,0,0,0,0,0,0,21,4,99,36,50,49,1,1,0,0,0,0,0,0,22,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C21_2words : List Nat := C21_2p0

theorem C21_2wire : C21_2.flatMap columnWords = C21_2words := by
  rfl

theorem C21_2wordBound : C21_2words.all wordBound = true := by
  simp only [C21_2words,List.all_append,C21_2p0bound]
  try rfl

theorem C21_2bounded : ∀ n ∈ C21_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C21_2wordBound

theorem C21_2length : C21_2.length = 7 := by rfl

def M21 : Module := ⟨21, [107,101,99,95,105,111,116,97], false, false, C21_0 ++ C21_1 ++ C21_2, ((List.range 0).map (fun n => [n]))⟩

def M21prefix : List Nat := [21,8,107,101,99,95,105,111,116,97,0,0,0,0,23]
theorem M21prefixwordBound : M21prefix.all wordBound = true := by decide

def M21words : List Nat := M21prefix ++ C21_0words ++ C21_1words ++ C21_2words ++ [0]

theorem M21wire : module.encode M21 = M21words := by
  rw [module_fast]
  simp only [M21,moduleWords,List.length_append,List.flatMap_append,C21_0length,C21_1length,C21_2length,C21_0wire,C21_1wire,C21_2wire]
  rfl

theorem M21wordBound : M21words.all wordBound = true := by
  simp only [M21words,List.all_append,M21prefixwordBound,C21_0wordBound,C21_1wordBound,C21_2wordBound]
  decide

theorem M21bounded : ∀ n ∈ M21words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M21wordBound

end DivRemFV.Replay
