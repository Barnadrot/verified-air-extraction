import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C15_0 : List Column := [⟨0, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨3, [107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨4, [106], (some (5)), false, false, false⟩,⟨5, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,51], (some (16)), false, false, false⟩,⟨6, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,50], (some (16)), false, false, false⟩,⟨7, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,49], (some (16)), false, false, false⟩]

def C15_0p0 : List Nat := [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0]
theorem C15_0p0bound : C15_0p0.all wordBound = true := (by decide : [0,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,20,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,24,107,101,99,99,97,107,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C15_0p1 : List Nat := [4,1,106,1,5,0,0,0,0,0,0,5,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,51,1,16,0,0,0,0,0,0,6,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,50,1,16,0,0,0,0,0,0,7,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,49,1,16,0,0,0,0,0,0]
theorem C15_0p1bound : C15_0p1.all wordBound = true := (by decide : [4,1,106,1,5,0,0,0,0,0,0,5,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,51,1,16,0,0,0,0,0,0,6,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,50,1,16,0,0,0,0,0,0,7,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C15_0words : List Nat := C15_0p0 ++ C15_0p1

theorem C15_0wire : C15_0.flatMap columnWords = C15_0words := by
  rfl

theorem C15_0wordBound : C15_0words.all wordBound = true := by
  simp only [C15_0words,List.all_append,C15_0p0bound,C15_0p1bound]
  try rfl

theorem C15_0bounded : ∀ n ∈ C15_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C15_0wordBound

theorem C15_0length : C15_0.length = 8 := by rfl

def C15_1 : List Column := [⟨8, [114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,48], (some (16)), false, false, false⟩,⟨9, [108,99,109,36,50], (some (5)), false, false, false⟩,⟨10, [108,99,109,36,51], (some (1)), false, false, false⟩,⟨11, [115,116,97,109,112,36,54,39,49], (some (16)), false, false, false⟩,⟨12, [115,116,97,109,112,36,54,39,48], (some (16)), false, false, false⟩,⟨13, [102,108,97,36,49,51], (some (16)), false, false, false⟩,⟨14, [102,108,97,36,49,52], (some (16)), false, false, false⟩,⟨15, [36,114,101,116], (some (1)), false, false, false⟩]

def C15_1p0 : List Nat := [8,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,48,1,16,0,0,0,0,0,0,9,5,108,99,109,36,50,1,5,0,0,0,0,0,0,10,5,108,99,109,36,51,1,1,0,0,0,0,0,0,11,9,115,116,97,109,112,36,54,39,49,1,16,0,0,0,0,0,0,12,9,115,116,97,109,112,36,54,39,48,1,16,0,0,0,0,0,0,13,6,102,108,97,36,49,51,1,16,0,0,0,0,0,0,14,6,102,108,97,36,49,52,1,16,0,0,0,0,0,0,15,4]
theorem C15_1p0bound : C15_1p0.all wordBound = true := (by decide : [8,16,114,111,117,110,100,95,99,111,110,115,116,97,110,116,39,48,1,16,0,0,0,0,0,0,9,5,108,99,109,36,50,1,5,0,0,0,0,0,0,10,5,108,99,109,36,51,1,1,0,0,0,0,0,0,11,9,115,116,97,109,112,36,54,39,49,1,16,0,0,0,0,0,0,12,9,115,116,97,109,112,36,54,39,48,1,16,0,0,0,0,0,0,13,6,102,108,97,36,49,51,1,16,0,0,0,0,0,0,14,6,102,108,97,36,49,52,1,16,0,0,0,0,0,0,15,4].all wordBound = true)

def C15_1p1 : List Nat := [36,114,101,116,1,1,0,0,0,0,0,0]
theorem C15_1p1bound : C15_1p1.all wordBound = true := (by decide : [36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C15_1words : List Nat := C15_1p0 ++ C15_1p1

theorem C15_1wire : C15_1.flatMap columnWords = C15_1words := by
  rfl

theorem C15_1wordBound : C15_1words.all wordBound = true := by
  simp only [C15_1words,List.all_append,C15_1p0bound,C15_1p1bound]
  try rfl

theorem C15_1bounded : ∀ n ∈ C15_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C15_1wordBound

theorem C15_1length : C15_1.length = 8 := by rfl

def C15_2 : List Column := [⟨16, [36,112,99], (some (2)), false, false, false⟩,⟨17, [36,105,115,95,112,99,95,49], (some (1)), false, false, false⟩,⟨18, [36,105,115,95,112,99,95,50], (some (1)), false, false, false⟩,⟨19, [36,108,111,111,107,117,112,95,115,101,108,95,49,57], (some (1)), false, false, false⟩,⟨20, [36,108,111,111,107,117,112,95,115,101,108,95,50,48], (some (1)), false, false, false⟩,⟨21, [40,105,110,118,32,107,101,99,99,97,107,95,102,58,36,112,99,41], none, false, false, true⟩]

def C15_2p0 : List Nat := [16,3,36,112,99,1,2,0,0,0,0,0,0,17,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,18,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,19,14,36,108,111,111,107,117,112,95,115,101,108,95,49,57,1,1,0,0,0,0,0,0,20,14,36,108,111,111,107,117,112,95,115,101,108,95,50,48,1,1,0,0,0,0,0,0,21,18,40,105,110,118,32,107,101,99,99,97,107,95,102,58,36,112,99,41,0,0,0,0,0,0,1,0]
theorem C15_2p0bound : C15_2p0.all wordBound = true := (by decide : [16,3,36,112,99,1,2,0,0,0,0,0,0,17,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,18,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,19,14,36,108,111,111,107,117,112,95,115,101,108,95,49,57,1,1,0,0,0,0,0,0,20,14,36,108,111,111,107,117,112,95,115,101,108,95,50,48,1,1,0,0,0,0,0,0,21,18,40,105,110,118,32,107,101,99,99,97,107,95,102,58,36,112,99,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C15_2words : List Nat := C15_2p0

theorem C15_2wire : C15_2.flatMap columnWords = C15_2words := by
  rfl

theorem C15_2wordBound : C15_2words.all wordBound = true := by
  simp only [C15_2words,List.all_append,C15_2p0bound]
  try rfl

theorem C15_2bounded : ∀ n ∈ C15_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C15_2wordBound

theorem C15_2length : C15_2.length = 6 := by rfl

def M15 : Module := ⟨15, [107,101,99,99,97,107,95,102], false, false, C15_0 ++ C15_1 ++ C15_2, ((List.range 0).map (fun n => [n]))⟩

def M15prefix : List Nat := [15,8,107,101,99,99,97,107,95,102,0,0,0,0,22]
theorem M15prefixwordBound : M15prefix.all wordBound = true := by decide

def M15words : List Nat := M15prefix ++ C15_0words ++ C15_1words ++ C15_2words ++ [0]

theorem M15wire : module.encode M15 = M15words := by
  rw [module_fast]
  simp only [M15,moduleWords,List.length_append,List.flatMap_append,C15_0length,C15_1length,C15_2length,C15_0wire,C15_1wire,C15_2wire]
  rfl

theorem M15wordBound : M15words.all wordBound = true := by
  simp only [M15words,List.all_append,M15prefixwordBound,C15_0wordBound,C15_1wordBound,C15_2wordBound]
  decide

theorem M15bounded : ∀ n ∈ M15words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M15wordBound

end DivRemFV.Replay
