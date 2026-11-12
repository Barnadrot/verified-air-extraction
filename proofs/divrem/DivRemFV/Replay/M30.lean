import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C30_0 : List Column := [⟨0, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [114], (some (5)), true, false, false⟩,⟨3, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨4, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨5, [105], (some (5)), false, false, false⟩,⟨6, [36,50], none, false, false, true⟩,⟨7, [36,51], none, false, false, true⟩]

def C30_0p0 : List Nat := [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,1,114,1,5,1,0,0,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,4,27,112,111,115,101,105,100,111,110,50,95,115,116]
theorem C30_0p0bound : C30_0p0.all wordBound = true := (by decide : [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,1,114,1,5,1,0,0,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,4,27,112,111,115,101,105,100,111,110,50,95,115,116].all wordBound = true)

def C30_0p1 : List Nat := [97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,5,1,105,1,5,0,0,0,0,0,0,6,2,36,50,0,0,0,0,0,0,1,0,7,2,36,51,0,0,0,0,0,0,1,0]
theorem C30_0p1bound : C30_0p1.all wordBound = true := (by decide : [97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,5,1,105,1,5,0,0,0,0,0,0,6,2,36,50,0,0,0,0,0,0,1,0,7,2,36,51,0,0,0,0,0,0,1,0].all wordBound = true)

def C30_0words : List Nat := C30_0p0 ++ C30_0p1

theorem C30_0wire : C30_0.flatMap columnWords = C30_0words := by
  rfl

theorem C30_0wordBound : C30_0words.all wordBound = true := by
  simp only [C30_0words,List.all_append,C30_0p0bound,C30_0p1bound]
  try rfl

theorem C30_0bounded : ∀ n ∈ C30_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C30_0wordBound

theorem C30_0length : C30_0.length = 8 := by rfl

def C30_1 : List Column := [⟨8, [108,99,109,36,52], (some (5)), false, false, false⟩,⟨9, [108,99,109,36,53], (some (1)), false, false, false⟩,⟨10, [115,116,97,109,112,36,56,39,49], (some (16)), false, false, false⟩,⟨11, [115,116,97,109,112,36,56,39,48], (some (16)), false, false, false⟩,⟨12, [115,116,97,109,112,36,57,39,49], (some (16)), false, false, false⟩,⟨13, [115,116,97,109,112,36,57,39,48], (some (16)), false, false, false⟩,⟨14, [99,36,50,48], (some (1)), false, false, false⟩,⟨15, [99,36,50,49], (some (1)), false, false, false⟩]

def C30_1p0 : List Nat := [8,5,108,99,109,36,52,1,5,0,0,0,0,0,0,9,5,108,99,109,36,53,1,1,0,0,0,0,0,0,10,9,115,116,97,109,112,36,56,39,49,1,16,0,0,0,0,0,0,11,9,115,116,97,109,112,36,56,39,48,1,16,0,0,0,0,0,0,12,9,115,116,97,109,112,36,57,39,49,1,16,0,0,0,0,0,0,13,9,115,116,97,109,112,36,57,39,48,1,16,0,0,0,0,0,0,14,4,99,36,50,48,1,1,0,0,0,0,0,0,15,4,99,36,50,49,1,1]
theorem C30_1p0bound : C30_1p0.all wordBound = true := (by decide : [8,5,108,99,109,36,52,1,5,0,0,0,0,0,0,9,5,108,99,109,36,53,1,1,0,0,0,0,0,0,10,9,115,116,97,109,112,36,56,39,49,1,16,0,0,0,0,0,0,11,9,115,116,97,109,112,36,56,39,48,1,16,0,0,0,0,0,0,12,9,115,116,97,109,112,36,57,39,49,1,16,0,0,0,0,0,0,13,9,115,116,97,109,112,36,57,39,48,1,16,0,0,0,0,0,0,14,4,99,36,50,48,1,1,0,0,0,0,0,0,15,4,99,36,50,49,1,1].all wordBound = true)

def C30_1p1 : List Nat := [0,0,0,0,0,0]
theorem C30_1p1bound : C30_1p1.all wordBound = true := (by decide : [0,0,0,0,0,0].all wordBound = true)

def C30_1words : List Nat := C30_1p0 ++ C30_1p1

theorem C30_1wire : C30_1.flatMap columnWords = C30_1words := by
  rfl

theorem C30_1wordBound : C30_1words.all wordBound = true := by
  simp only [C30_1words,List.all_append,C30_1p0bound,C30_1p1bound]
  try rfl

theorem C30_1bounded : ∀ n ∈ C30_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C30_1wordBound

theorem C30_1length : C30_1.length = 8 := by rfl

def C30_2 : List Column := [⟨16, [102,108,97,36,49,54], (some (16)), false, false, false⟩,⟨17, [102,108,97,36,49,55], (some (16)), false, false, false⟩,⟨18, [102,108,97,36,49,56], (some (16)), false, false, false⟩,⟨19, [102,108,97,36,49,57], (some (16)), false, false, false⟩,⟨20, [36,114,101,116], (some (1)), false, false, false⟩,⟨21, [36,112,99], (some (2)), false, false, false⟩,⟨22, [36,105,115,95,112,99,95,49], (some (1)), false, false, false⟩,⟨23, [36,105,115,95,112,99,95,50], (some (1)), false, false, false⟩]

def C30_2p0 : List Nat := [16,6,102,108,97,36,49,54,1,16,0,0,0,0,0,0,17,6,102,108,97,36,49,55,1,16,0,0,0,0,0,0,18,6,102,108,97,36,49,56,1,16,0,0,0,0,0,0,19,6,102,108,97,36,49,57,1,16,0,0,0,0,0,0,20,4,36,114,101,116,1,1,0,0,0,0,0,0,21,3,36,112,99,1,2,0,0,0,0,0,0,22,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,23,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0]
theorem C30_2p0bound : C30_2p0.all wordBound = true := (by decide : [16,6,102,108,97,36,49,54,1,16,0,0,0,0,0,0,17,6,102,108,97,36,49,55,1,16,0,0,0,0,0,0,18,6,102,108,97,36,49,56,1,16,0,0,0,0,0,0,19,6,102,108,97,36,49,57,1,16,0,0,0,0,0,0,20,4,36,114,101,116,1,1,0,0,0,0,0,0,21,3,36,112,99,1,2,0,0,0,0,0,0,22,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,23,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0].all wordBound = true)

def C30_2words : List Nat := C30_2p0

theorem C30_2wire : C30_2.flatMap columnWords = C30_2words := by
  rfl

theorem C30_2wordBound : C30_2words.all wordBound = true := by
  simp only [C30_2words,List.all_append,C30_2p0bound]
  try rfl

theorem C30_2bounded : ∀ n ∈ C30_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C30_2wordBound

theorem C30_2length : C30_2.length = 8 := by rfl

def C30_3 : List Column := [⟨24, [36,108,111,111,107,117,112,95,115,101,108,95,50,52], (some (1)), false, false, false⟩,⟨25, [36,108,111,111,107,117,112,95,115,101,108,95,50,53], (some (1)), false, false, false⟩,⟨26, [36,108,111,111,107,117,112,95,115,101,108,95,50,54], (some (1)), false, false, false⟩,⟨27, [36,108,111,111,107,117,112,95,115,101,108,95,50,55], (some (1)), false, false, false⟩,⟨28, [40,105,110,118,32,102,117,108,108,95,114,111,117,110,100,58,36,112,99,41], none, false, false, true⟩]

def C30_3p0 : List Nat := [24,14,36,108,111,111,107,117,112,95,115,101,108,95,50,52,1,1,0,0,0,0,0,0,25,14,36,108,111,111,107,117,112,95,115,101,108,95,50,53,1,1,0,0,0,0,0,0,26,14,36,108,111,111,107,117,112,95,115,101,108,95,50,54,1,1,0,0,0,0,0,0,27,14,36,108,111,111,107,117,112,95,115,101,108,95,50,55,1,1,0,0,0,0,0,0,28,20,40,105,110,118,32,102,117,108,108,95,114,111,117,110,100,58,36,112,99,41,0,0,0,0,0,0,1,0]
theorem C30_3p0bound : C30_3p0.all wordBound = true := (by decide : [24,14,36,108,111,111,107,117,112,95,115,101,108,95,50,52,1,1,0,0,0,0,0,0,25,14,36,108,111,111,107,117,112,95,115,101,108,95,50,53,1,1,0,0,0,0,0,0,26,14,36,108,111,111,107,117,112,95,115,101,108,95,50,54,1,1,0,0,0,0,0,0,27,14,36,108,111,111,107,117,112,95,115,101,108,95,50,55,1,1,0,0,0,0,0,0,28,20,40,105,110,118,32,102,117,108,108,95,114,111,117,110,100,58,36,112,99,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C30_3words : List Nat := C30_3p0

theorem C30_3wire : C30_3.flatMap columnWords = C30_3words := by
  rfl

theorem C30_3wordBound : C30_3words.all wordBound = true := by
  simp only [C30_3words,List.all_append,C30_3p0bound]
  try rfl

theorem C30_3bounded : ∀ n ∈ C30_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C30_3wordBound

theorem C30_3length : C30_3.length = 5 := by rfl

def M30 : Module := ⟨30, [102,117,108,108,95,114,111,117,110,100], false, false, C30_0 ++ C30_1 ++ C30_2 ++ C30_3, ((List.range 0).map (fun n => [n]))⟩

def M30prefix : List Nat := [30,10,102,117,108,108,95,114,111,117,110,100,0,0,0,0,29]
theorem M30prefixwordBound : M30prefix.all wordBound = true := by decide

def M30words : List Nat := M30prefix ++ C30_0words ++ C30_1words ++ C30_2words ++ C30_3words ++ [0]

theorem M30wire : module.encode M30 = M30words := by
  rw [module_fast]
  simp only [M30,moduleWords,List.length_append,List.flatMap_append,C30_0length,C30_1length,C30_2length,C30_3length,C30_0wire,C30_1wire,C30_2wire,C30_3wire]
  rfl

theorem M30wordBound : M30words.all wordBound = true := by
  simp only [M30words,List.all_append,M30prefixwordBound,C30_0wordBound,C30_1wordBound,C30_2wordBound,C30_3wordBound]
  decide

theorem M30bounded : ∀ n ∈ M30words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M30wordBound

end DivRemFV.Replay
