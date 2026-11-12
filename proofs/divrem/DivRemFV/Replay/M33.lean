import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C33_0 : List Column := [⟨0, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [114], (some (5)), true, false, false⟩,⟨3, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨4, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨5, [105,110,100,101,120], (some (10)), false, false, false⟩,⟨6, [36,50], (some (10)), false, false, false⟩,⟨7, [36,51], (some (5)), false, false, false⟩]

def C33_0p0 : List Nat := [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,1,114,1,5,1,0,0,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,4,27,112,111,115,101,105,100,111,110,50,95,115,116]
theorem C33_0p0bound : C33_0p0.all wordBound = true := (by decide : [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,1,114,1,5,1,0,0,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,4,27,112,111,115,101,105,100,111,110,50,95,115,116].all wordBound = true)

def C33_0p1 : List Nat := [97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,5,5,105,110,100,101,120,1,10,0,0,0,0,0,0,6,2,36,50,1,10,0,0,0,0,0,0,7,2,36,51,1,5,0,0,0,0,0,0]
theorem C33_0p1bound : C33_0p1.all wordBound = true := (by decide : [97,116,101,36,115,116,97,109,112,95,111,117,116,39,48,1,16,0,0,1,0,0,0,5,5,105,110,100,101,120,1,10,0,0,0,0,0,0,6,2,36,50,1,10,0,0,0,0,0,0,7,2,36,51,1,5,0,0,0,0,0,0].all wordBound = true)

def C33_0words : List Nat := C33_0p0 ++ C33_0p1

theorem C33_0wire : C33_0.flatMap columnWords = C33_0words := by
  rfl

theorem C33_0wordBound : C33_0words.all wordBound = true := by
  simp only [C33_0words,List.all_append,C33_0p0bound,C33_0p1bound]
  try rfl

theorem C33_0bounded : ∀ n ∈ C33_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C33_0wordBound

theorem C33_0length : C33_0.length = 8 := by rfl

def C33_1 : List Column := [⟨8, [36,52], none, false, false, true⟩,⟨9, [36,53], none, false, false, true⟩,⟨10, [36,54], (some (5)), false, false, false⟩,⟨11, [36,55], none, false, false, true⟩,⟨12, [115,116,97,109,112,36,49,48,39,49], (some (16)), false, false, false⟩,⟨13, [115,116,97,109,112,36,49,48,39,48], (some (16)), false, false, false⟩,⟨14, [99,36,49,52], (some (1)), false, false, false⟩,⟨15, [99,36,49,53], (some (1)), false, false, false⟩]

def C33_1p0 : List Nat := [8,2,36,52,0,0,0,0,0,0,1,0,9,2,36,53,0,0,0,0,0,0,1,0,10,2,36,54,1,5,0,0,0,0,0,0,11,2,36,55,0,0,0,0,0,0,1,0,12,10,115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0,13,10,115,116,97,109,112,36,49,48,39,48,1,16,0,0,0,0,0,0,14,4,99,36,49,52,1,1,0,0,0,0,0,0,15,4,99,36,49,53,1,1,0,0,0,0,0,0]
theorem C33_1p0bound : C33_1p0.all wordBound = true := (by decide : [8,2,36,52,0,0,0,0,0,0,1,0,9,2,36,53,0,0,0,0,0,0,1,0,10,2,36,54,1,5,0,0,0,0,0,0,11,2,36,55,0,0,0,0,0,0,1,0,12,10,115,116,97,109,112,36,49,48,39,49,1,16,0,0,0,0,0,0,13,10,115,116,97,109,112,36,49,48,39,48,1,16,0,0,0,0,0,0,14,4,99,36,49,52,1,1,0,0,0,0,0,0,15,4,99,36,49,53,1,1,0,0,0,0,0,0].all wordBound = true)

def C33_1words : List Nat := C33_1p0

theorem C33_1wire : C33_1.flatMap columnWords = C33_1words := by
  rfl

theorem C33_1wordBound : C33_1words.all wordBound = true := by
  simp only [C33_1words,List.all_append,C33_1p0bound]
  try rfl

theorem C33_1bounded : ∀ n ∈ C33_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C33_1wordBound

theorem C33_1length : C33_1.length = 8 := by rfl

def C33_2 : List Column := [⟨16, [36,114,101,116], (some (1)), false, false, false⟩]

def C33_2p0 : List Nat := [16,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C33_2p0bound : C33_2p0.all wordBound = true := (by decide : [16,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C33_2words : List Nat := C33_2p0

theorem C33_2wire : C33_2.flatMap columnWords = C33_2words := by
  rfl

theorem C33_2wordBound : C33_2words.all wordBound = true := by
  simp only [C33_2words,List.all_append,C33_2p0bound]
  try rfl

theorem C33_2bounded : ∀ n ∈ C33_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C33_2wordBound

theorem C33_2length : C33_2.length = 1 := by rfl

def M33 : Module := ⟨33, [97,100,100,95,114,111,117,110,100,95,107,101,121,95,112,97,114,116,105,97,108], false, false, C33_0 ++ C33_1 ++ C33_2, ((List.range 0).map (fun n => [n]))⟩

def M33prefix : List Nat := [33,21,97,100,100,95,114,111,117,110,100,95,107,101,121,95,112,97,114,116,105,97,108,0,0,0,0,17]
theorem M33prefixwordBound : M33prefix.all wordBound = true := by decide

def M33words : List Nat := M33prefix ++ C33_0words ++ C33_1words ++ C33_2words ++ [0]

theorem M33wire : module.encode M33 = M33words := by
  rw [module_fast]
  simp only [M33,moduleWords,List.length_append,List.flatMap_append,C33_0length,C33_1length,C33_2length,C33_0wire,C33_1wire,C33_2wire]
  rfl

theorem M33wordBound : M33words.all wordBound = true := by
  simp only [M33words,List.all_append,M33prefixwordBound,C33_0wordBound,C33_1wordBound,C33_2wordBound]
  decide

theorem M33bounded : ∀ n ∈ M33words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M33wordBound

end DivRemFV.Replay
