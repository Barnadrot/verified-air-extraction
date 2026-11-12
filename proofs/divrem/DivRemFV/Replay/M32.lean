import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C32_0 : List Column := [⟨0, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [114], (some (5)), true, false, false⟩,⟨3, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨4, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨5, [105,110,100,101,120], (some (10)), false, false, false⟩,⟨6, [105], (some (5)), false, false, false⟩,⟨7, [36,51], (some (10)), false, false, false⟩]

def C32_0p0 : List Nat := [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,1,114,1,5,1,0,0,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,4,27,112,111,115,101,105,100,111,110,50,95,115,116]
theorem C32_0p0bound : C32_0p0.all wordBound = true := (by decide : [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,1,114,1,5,1,0,0,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,4,27,112,111,115,101,105,100,111,110,50,95,115,116].all wordBound = true)

def C32_0p1 : List Nat := [97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,5,5,105,110,100,101,120,1,10,0,0,0,0,0,0,6,1,105,1,5,0,0,0,0,0,0,7,2,36,51,1,10,0,0,0,0,0,0]
theorem C32_0p1bound : C32_0p1.all wordBound = true := (by decide : [97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,5,5,105,110,100,101,120,1,10,0,0,0,0,0,0,6,1,105,1,5,0,0,0,0,0,0,7,2,36,51,1,10,0,0,0,0,0,0].all wordBound = true)

def C32_0words : List Nat := C32_0p0 ++ C32_0p1

theorem C32_0wire : C32_0.flatMap columnWords = C32_0words := by
  rfl

theorem C32_0wordBound : C32_0words.all wordBound = true := by
  simp only [C32_0words,List.all_append,C32_0p0bound,C32_0p1bound]
  try rfl

theorem C32_0bounded : ∀ n ∈ C32_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C32_0wordBound

theorem C32_0length : C32_0.length = 8 := by rfl

def C32_1 : List Column := [⟨8, [36,52], none, false, false, true⟩,⟨9, [36,53], none, false, false, true⟩,⟨10, [36,54], none, false, false, true⟩,⟨11, [108,99,109,36,55], (some (5)), false, false, false⟩,⟨12, [108,99,109,36,56], (some (1)), false, false, false⟩,⟨13, [115,116,97,109,112,36,49,49,39,49], (some (16)), false, false, false⟩,⟨14, [115,116,97,109,112,36,49,49,39,48], (some (16)), false, false, false⟩,⟨15, [99,36,49,55], (some (1)), false, false, false⟩]

def C32_1p0 : List Nat := [8,2,36,52,0,0,0,0,0,0,1,0,9,2,36,53,0,0,0,0,0,0,1,0,10,2,36,54,0,0,0,0,0,0,1,0,11,5,108,99,109,36,55,1,5,0,0,0,0,0,0,12,5,108,99,109,36,56,1,1,0,0,0,0,0,0,13,10,115,116,97,109,112,36,49,49,39,49,1,16,0,0,0,0,0,0,14,10,115,116,97,109,112,36,49,49,39,48,1,16,0,0,0,0,0,0,15,4,99,36,49,55,1,1,0,0,0,0,0,0]
theorem C32_1p0bound : C32_1p0.all wordBound = true := (by decide : [8,2,36,52,0,0,0,0,0,0,1,0,9,2,36,53,0,0,0,0,0,0,1,0,10,2,36,54,0,0,0,0,0,0,1,0,11,5,108,99,109,36,55,1,5,0,0,0,0,0,0,12,5,108,99,109,36,56,1,1,0,0,0,0,0,0,13,10,115,116,97,109,112,36,49,49,39,49,1,16,0,0,0,0,0,0,14,10,115,116,97,109,112,36,49,49,39,48,1,16,0,0,0,0,0,0,15,4,99,36,49,55,1,1,0,0,0,0,0,0].all wordBound = true)

def C32_1words : List Nat := C32_1p0

theorem C32_1wire : C32_1.flatMap columnWords = C32_1words := by
  rfl

theorem C32_1wordBound : C32_1words.all wordBound = true := by
  simp only [C32_1words,List.all_append,C32_1p0bound]
  try rfl

theorem C32_1bounded : ∀ n ∈ C32_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C32_1wordBound

theorem C32_1length : C32_1.length = 8 := by rfl

def C32_2 : List Column := [⟨16, [99,36,49,56], (some (1)), false, false, false⟩,⟨17, [102,108,97,36,49,55], (some (16)), false, false, false⟩,⟨18, [102,108,97,36,49,56], (some (16)), false, false, false⟩,⟨19, [36,114,101,116], (some (1)), false, false, false⟩,⟨20, [36,112,99], (some (2)), false, false, false⟩,⟨21, [36,105,115,95,112,99,95,49], (some (1)), false, false, false⟩,⟨22, [36,105,115,95,112,99,95,50], (some (1)), false, false, false⟩,⟨23, [36,108,111,111,107,117,112,95,115,101,108,95,50,51], (some (1)), false, false, false⟩]

def C32_2p0 : List Nat := [16,4,99,36,49,56,1,1,0,0,0,0,0,0,17,6,102,108,97,36,49,55,1,16,0,0,0,0,0,0,18,6,102,108,97,36,49,56,1,16,0,0,0,0,0,0,19,4,36,114,101,116,1,1,0,0,0,0,0,0,20,3,36,112,99,1,2,0,0,0,0,0,0,21,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,22,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,23,14,36,108,111,111,107,117,112,95,115,101,108,95,50,51,1,1,0]
theorem C32_2p0bound : C32_2p0.all wordBound = true := (by decide : [16,4,99,36,49,56,1,1,0,0,0,0,0,0,17,6,102,108,97,36,49,55,1,16,0,0,0,0,0,0,18,6,102,108,97,36,49,56,1,16,0,0,0,0,0,0,19,4,36,114,101,116,1,1,0,0,0,0,0,0,20,3,36,112,99,1,2,0,0,0,0,0,0,21,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,22,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0,23,14,36,108,111,111,107,117,112,95,115,101,108,95,50,51,1,1,0].all wordBound = true)

def C32_2p1 : List Nat := [0,0,0,0,0]
theorem C32_2p1bound : C32_2p1.all wordBound = true := (by decide : [0,0,0,0,0].all wordBound = true)

def C32_2words : List Nat := C32_2p0 ++ C32_2p1

theorem C32_2wire : C32_2.flatMap columnWords = C32_2words := by
  rfl

theorem C32_2wordBound : C32_2words.all wordBound = true := by
  simp only [C32_2words,List.all_append,C32_2p0bound,C32_2p1bound]
  try rfl

theorem C32_2bounded : ∀ n ∈ C32_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C32_2wordBound

theorem C32_2length : C32_2.length = 8 := by rfl

def C32_3 : List Column := [⟨24, [36,108,111,111,107,117,112,95,115,101,108,95,50,52], (some (1)), false, false, false⟩,⟨25, [40,105,110,118,32,97,100,100,95,114,111,117,110,100,95,107,101,121,95,102,117,108,108,58,36,112,99,41], none, false, false, true⟩]

def C32_3p0 : List Nat := [24,14,36,108,111,111,107,117,112,95,115,101,108,95,50,52,1,1,0,0,0,0,0,0,25,28,40,105,110,118,32,97,100,100,95,114,111,117,110,100,95,107,101,121,95,102,117,108,108,58,36,112,99,41,0,0,0,0,0,0,1,0]
theorem C32_3p0bound : C32_3p0.all wordBound = true := (by decide : [24,14,36,108,111,111,107,117,112,95,115,101,108,95,50,52,1,1,0,0,0,0,0,0,25,28,40,105,110,118,32,97,100,100,95,114,111,117,110,100,95,107,101,121,95,102,117,108,108,58,36,112,99,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C32_3words : List Nat := C32_3p0

theorem C32_3wire : C32_3.flatMap columnWords = C32_3words := by
  rfl

theorem C32_3wordBound : C32_3words.all wordBound = true := by
  simp only [C32_3words,List.all_append,C32_3p0bound]
  try rfl

theorem C32_3bounded : ∀ n ∈ C32_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C32_3wordBound

theorem C32_3length : C32_3.length = 2 := by rfl

def M32 : Module := ⟨32, [97,100,100,95,114,111,117,110,100,95,107,101,121,95,102,117,108,108], false, false, C32_0 ++ C32_1 ++ C32_2 ++ C32_3, ((List.range 0).map (fun n => [n]))⟩

def M32prefix : List Nat := [32,18,97,100,100,95,114,111,117,110,100,95,107,101,121,95,102,117,108,108,0,0,0,0,26]
theorem M32prefixwordBound : M32prefix.all wordBound = true := by decide

def M32words : List Nat := M32prefix ++ C32_0words ++ C32_1words ++ C32_2words ++ C32_3words ++ [0]

theorem M32wire : module.encode M32 = M32words := by
  rw [module_fast]
  simp only [M32,moduleWords,List.length_append,List.flatMap_append,C32_0length,C32_1length,C32_2length,C32_3length,C32_0wire,C32_1wire,C32_2wire,C32_3wire]
  rfl

theorem M32wordBound : M32words.all wordBound = true := by
  simp only [M32words,List.all_append,M32prefixwordBound,C32_0wordBound,C32_1wordBound,C32_2wordBound,C32_3wordBound]
  decide

theorem M32bounded : ∀ n ∈ M32words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M32wordBound

end DivRemFV.Replay
