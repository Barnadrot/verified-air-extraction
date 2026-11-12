import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C16_0 : List Column := [⟨0, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,51], (some (16)), true, false, false⟩,⟨3, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,50], (some (16)), true, false, false⟩,⟨4, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,49], (some (16)), true, false, false⟩,⟨5, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,48], (some (16)), true, false, false⟩,⟨6, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨7, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩]

def C16_0p0 : List Nat := [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,51,1,16,1,0,0,0,0,0,3,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,50,1,16,1,0,0,0,0,0,4,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116]
theorem C16_0p0bound : C16_0p0.all wordBound = true := (by decide : [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,51,1,16,1,0,0,0,0,0,3,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,50,1,16,1,0,0,0,0,0,4,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116].all wordBound = true)

def C16_0p1 : List Nat := [39,49,1,16,1,0,0,0,0,0,5,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,48,1,16,1,0,0,0,0,0,6,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,7,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0]
theorem C16_0p1bound : C16_0p1.all wordBound = true := (by decide : [39,49,1,16,1,0,0,0,0,0,5,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,48,1,16,1,0,0,0,0,0,6,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,7,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C16_0words : List Nat := C16_0p0 ++ C16_0p1

theorem C16_0wire : C16_0.flatMap columnWords = C16_0words := by
  rfl

theorem C16_0wordBound : C16_0words.all wordBound = true := by
  simp only [C16_0words,List.all_append,C16_0p0bound,C16_0p1bound]
  try rfl

theorem C16_0bounded : ∀ n ∈ C16_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C16_0wordBound

theorem C16_0length : C16_0.length = 8 := by rfl

def C16_1 : List Column := [⟨8, [115,116,97,109,112,36,51,39,49], (some (16)), false, false, false⟩,⟨9, [115,116,97,109,112,36,51,39,48], (some (16)), false, false, false⟩,⟨10, [115,116,97,109,112,36,52,39,49], (some (16)), false, false, false⟩,⟨11, [115,116,97,109,112,36,52,39,48], (some (16)), false, false, false⟩,⟨12, [115,116,97,109,112,36,53,39,49], (some (16)), false, false, false⟩,⟨13, [115,116,97,109,112,36,53,39,48], (some (16)), false, false, false⟩,⟨14, [115,116,97,109,112,36,54,39,49], (some (16)), false, false, false⟩,⟨15, [115,116,97,109,112,36,54,39,48], (some (16)), false, false, false⟩]

def C16_1p0 : List Nat := [8,9,115,116,97,109,112,36,51,39,49,1,16,0,0,0,0,0,0,9,9,115,116,97,109,112,36,51,39,48,1,16,0,0,0,0,0,0,10,9,115,116,97,109,112,36,52,39,49,1,16,0,0,0,0,0,0,11,9,115,116,97,109,112,36,52,39,48,1,16,0,0,0,0,0,0,12,9,115,116,97,109,112,36,53,39,49,1,16,0,0,0,0,0,0,13,9,115,116,97,109,112,36,53,39,48,1,16,0,0,0,0,0,0,14,9,115,116,97,109,112,36,54,39,49,1,16,0]
theorem C16_1p0bound : C16_1p0.all wordBound = true := (by decide : [8,9,115,116,97,109,112,36,51,39,49,1,16,0,0,0,0,0,0,9,9,115,116,97,109,112,36,51,39,48,1,16,0,0,0,0,0,0,10,9,115,116,97,109,112,36,52,39,49,1,16,0,0,0,0,0,0,11,9,115,116,97,109,112,36,52,39,48,1,16,0,0,0,0,0,0,12,9,115,116,97,109,112,36,53,39,49,1,16,0,0,0,0,0,0,13,9,115,116,97,109,112,36,53,39,48,1,16,0,0,0,0,0,0,14,9,115,116,97,109,112,36,54,39,49,1,16,0].all wordBound = true)

def C16_1p1 : List Nat := [0,0,0,0,0,15,9,115,116,97,109,112,36,54,39,48,1,16,0,0,0,0,0,0]
theorem C16_1p1bound : C16_1p1.all wordBound = true := (by decide : [0,0,0,0,0,15,9,115,116,97,109,112,36,54,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C16_1words : List Nat := C16_1p0 ++ C16_1p1

theorem C16_1wire : C16_1.flatMap columnWords = C16_1words := by
  rfl

theorem C16_1wordBound : C16_1words.all wordBound = true := by
  simp only [C16_1words,List.all_append,C16_1p0bound,C16_1p1bound]
  try rfl

theorem C16_1bounded : ∀ n ∈ C16_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C16_1wordBound

theorem C16_1length : C16_1.length = 8 := by rfl

def C16_2 : List Column := [⟨16, [115,116,97,109,112,36,55,39,49], (some (16)), false, false, false⟩,⟨17, [115,116,97,109,112,36,55,39,48], (some (16)), false, false, false⟩,⟨18, [36,114,101,116], (some (1)), false, false, false⟩]

def C16_2p0 : List Nat := [16,9,115,116,97,109,112,36,55,39,49,1,16,0,0,0,0,0,0,17,9,115,116,97,109,112,36,55,39,48,1,16,0,0,0,0,0,0,18,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C16_2p0bound : C16_2p0.all wordBound = true := (by decide : [16,9,115,116,97,109,112,36,55,39,49,1,16,0,0,0,0,0,0,17,9,115,116,97,109,112,36,55,39,48,1,16,0,0,0,0,0,0,18,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C16_2words : List Nat := C16_2p0

theorem C16_2wire : C16_2.flatMap columnWords = C16_2words := by
  rfl

theorem C16_2wordBound : C16_2words.all wordBound = true := by
  simp only [C16_2words,List.all_append,C16_2p0bound]
  try rfl

theorem C16_2bounded : ∀ n ∈ C16_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C16_2wordBound

theorem C16_2length : C16_2.length = 3 := by rfl

def M16 : Module := ⟨16, [107,101,99,99,97,107,95,102,95,114,111,117,110,100], false, false, C16_0 ++ C16_1 ++ C16_2, ((List.range 0).map (fun n => [n]))⟩

def M16prefix : List Nat := [16,14,107,101,99,99,97,107,95,102,95,114,111,117,110,100,0,0,0,0,19]
theorem M16prefixwordBound : M16prefix.all wordBound = true := by decide

def M16words : List Nat := M16prefix ++ C16_0words ++ C16_1words ++ C16_2words ++ [0]

theorem M16wire : module.encode M16 = M16words := by
  rw [module_fast]
  simp only [M16,moduleWords,List.length_append,List.flatMap_append,C16_0length,C16_1length,C16_2length,C16_0wire,C16_1wire,C16_2wire]
  rfl

theorem M16wordBound : M16words.all wordBound = true := by
  simp only [M16words,List.all_append,M16prefixwordBound,C16_0wordBound,C16_1wordBound,C16_2wordBound]
  decide

theorem M16bounded : ∀ n ∈ M16words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M16wordBound

end DivRemFV.Replay
