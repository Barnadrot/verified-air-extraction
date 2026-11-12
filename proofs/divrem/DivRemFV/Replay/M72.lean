import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C72_0 : List Column := [⟨0, [97,39,51], (some (16)), true, false, false⟩,⟨1, [97,39,50], (some (16)), true, false, false⟩,⟨2, [97,39,49], (some (16)), true, false, false⟩,⟨3, [97,39,48], (some (16)), true, false, false⟩,⟨4, [98,39,51], (some (16)), true, false, false⟩,⟨5, [98,39,50], (some (16)), true, false, false⟩,⟨6, [98,39,49], (some (16)), true, false, false⟩,⟨7, [98,39,48], (some (16)), true, false, false⟩]

def C72_0p0 : List Nat := [0,3,97,39,51,1,16,1,0,0,0,0,0,1,3,97,39,50,1,16,1,0,0,0,0,0,2,3,97,39,49,1,16,1,0,0,0,0,0,3,3,97,39,48,1,16,1,0,0,0,0,0,4,3,98,39,51,1,16,1,0,0,0,0,0,5,3,98,39,50,1,16,1,0,0,0,0,0,6,3,98,39,49,1,16,1,0,0,0,0,0,7,3,98,39,48,1,16,1,0,0,0,0,0]
theorem C72_0p0bound : C72_0p0.all wordBound = true := (by decide : [0,3,97,39,51,1,16,1,0,0,0,0,0,1,3,97,39,50,1,16,1,0,0,0,0,0,2,3,97,39,49,1,16,1,0,0,0,0,0,3,3,97,39,48,1,16,1,0,0,0,0,0,4,3,98,39,51,1,16,1,0,0,0,0,0,5,3,98,39,50,1,16,1,0,0,0,0,0,6,3,98,39,49,1,16,1,0,0,0,0,0,7,3,98,39,48,1,16,1,0,0,0,0,0].all wordBound = true)

def C72_0words : List Nat := C72_0p0

theorem C72_0wire : C72_0.flatMap columnWords = C72_0words := by
  rfl

theorem C72_0wordBound : C72_0words.all wordBound = true := by
  simp only [C72_0words,List.all_append,C72_0p0bound]
  try rfl

theorem C72_0bounded : ∀ n ∈ C72_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C72_0wordBound

theorem C72_0length : C72_0.length = 8 := by rfl

def C72_1 : List Column := [⟨8, [99,111,109,112,97,114,105,115,111,110], (some (1)), false, true, false⟩,⟨9, [97,95,115,105,103,110], (some (1)), false, false, false⟩,⟨10, [98,95,115,105,103,110], (some (1)), false, false, false⟩,⟨11, [97,95,115,117,102,102,105,120,39,51], (some (15)), false, false, false⟩,⟨12, [97,95,115,117,102,102,105,120,39,50], (some (16)), false, false, false⟩,⟨13, [97,95,115,117,102,102,105,120,39,49], (some (16)), false, false, false⟩,⟨14, [97,95,115,117,102,102,105,120,39,48], (some (16)), false, false, false⟩,⟨15, [98,95,115,117,102,102,105,120,39,51], (some (15)), false, false, false⟩]

def C72_1p0 : List Nat := [8,10,99,111,109,112,97,114,105,115,111,110,1,1,0,0,1,0,0,0,9,6,97,95,115,105,103,110,1,1,0,0,0,0,0,0,10,6,98,95,115,105,103,110,1,1,0,0,0,0,0,0,11,10,97,95,115,117,102,102,105,120,39,51,1,15,0,0,0,0,0,0,12,10,97,95,115,117,102,102,105,120,39,50,1,16,0,0,0,0,0,0,13,10,97,95,115,117,102,102,105,120,39,49,1,16,0,0,0,0,0,0,14,10,97,95,115,117,102,102,105,120,39,48,1,16,0,0]
theorem C72_1p0bound : C72_1p0.all wordBound = true := (by decide : [8,10,99,111,109,112,97,114,105,115,111,110,1,1,0,0,1,0,0,0,9,6,97,95,115,105,103,110,1,1,0,0,0,0,0,0,10,6,98,95,115,105,103,110,1,1,0,0,0,0,0,0,11,10,97,95,115,117,102,102,105,120,39,51,1,15,0,0,0,0,0,0,12,10,97,95,115,117,102,102,105,120,39,50,1,16,0,0,0,0,0,0,13,10,97,95,115,117,102,102,105,120,39,49,1,16,0,0,0,0,0,0,14,10,97,95,115,117,102,102,105,120,39,48,1,16,0,0].all wordBound = true)

def C72_1p1 : List Nat := [0,0,0,0,15,10,98,95,115,117,102,102,105,120,39,51,1,15,0,0,0,0,0,0]
theorem C72_1p1bound : C72_1p1.all wordBound = true := (by decide : [0,0,0,0,15,10,98,95,115,117,102,102,105,120,39,51,1,15,0,0,0,0,0,0].all wordBound = true)

def C72_1words : List Nat := C72_1p0 ++ C72_1p1

theorem C72_1wire : C72_1.flatMap columnWords = C72_1words := by
  rfl

theorem C72_1wordBound : C72_1words.all wordBound = true := by
  simp only [C72_1words,List.all_append,C72_1p0bound,C72_1p1bound]
  try rfl

theorem C72_1bounded : ∀ n ∈ C72_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C72_1wordBound

theorem C72_1length : C72_1.length = 8 := by rfl

def C72_2 : List Column := [⟨16, [98,95,115,117,102,102,105,120,39,50], (some (16)), false, false, false⟩,⟨17, [98,95,115,117,102,102,105,120,39,49], (some (16)), false, false, false⟩,⟨18, [98,95,115,117,102,102,105,120,39,48], (some (16)), false, false, false⟩,⟨19, [116,109,112,39,51], (some (16)), false, false, false⟩,⟨20, [116,109,112,39,50], (some (16)), false, false, false⟩,⟨21, [116,109,112,39,49], (some (16)), false, false, false⟩,⟨22, [116,109,112,39,48], (some (16)), false, false, false⟩,⟨23, [98,36,50,51], (some (1)), false, false, false⟩]

def C72_2p0 : List Nat := [16,10,98,95,115,117,102,102,105,120,39,50,1,16,0,0,0,0,0,0,17,10,98,95,115,117,102,102,105,120,39,49,1,16,0,0,0,0,0,0,18,10,98,95,115,117,102,102,105,120,39,48,1,16,0,0,0,0,0,0,19,5,116,109,112,39,51,1,16,0,0,0,0,0,0,20,5,116,109,112,39,50,1,16,0,0,0,0,0,0,21,5,116,109,112,39,49,1,16,0,0,0,0,0,0,22,5,116,109,112,39,48,1,16,0,0,0,0,0,0,23,4,98,36,50,51,1,1]
theorem C72_2p0bound : C72_2p0.all wordBound = true := (by decide : [16,10,98,95,115,117,102,102,105,120,39,50,1,16,0,0,0,0,0,0,17,10,98,95,115,117,102,102,105,120,39,49,1,16,0,0,0,0,0,0,18,10,98,95,115,117,102,102,105,120,39,48,1,16,0,0,0,0,0,0,19,5,116,109,112,39,51,1,16,0,0,0,0,0,0,20,5,116,109,112,39,50,1,16,0,0,0,0,0,0,21,5,116,109,112,39,49,1,16,0,0,0,0,0,0,22,5,116,109,112,39,48,1,16,0,0,0,0,0,0,23,4,98,36,50,51,1,1].all wordBound = true)

def C72_2p1 : List Nat := [0,0,0,0,0,0]
theorem C72_2p1bound : C72_2p1.all wordBound = true := (by decide : [0,0,0,0,0,0].all wordBound = true)

def C72_2words : List Nat := C72_2p0 ++ C72_2p1

theorem C72_2wire : C72_2.flatMap columnWords = C72_2words := by
  rfl

theorem C72_2wordBound : C72_2words.all wordBound = true := by
  simp only [C72_2words,List.all_append,C72_2p0bound,C72_2p1bound]
  try rfl

theorem C72_2bounded : ∀ n ∈ C72_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C72_2wordBound

theorem C72_2length : C72_2.length = 8 := by rfl

def C72_3 : List Column := [⟨24, [98,36,50,52], (some (1)), false, false, false⟩,⟨25, [98,36,50,53], (some (1)), false, false, false⟩,⟨26, [98,36,50,54], (some (1)), false, false, false⟩,⟨27, [36,114,101,116], (some (1)), false, false, false⟩]

def C72_3p0 : List Nat := [24,4,98,36,50,52,1,1,0,0,0,0,0,0,25,4,98,36,50,53,1,1,0,0,0,0,0,0,26,4,98,36,50,54,1,1,0,0,0,0,0,0,27,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C72_3p0bound : C72_3p0.all wordBound = true := (by decide : [24,4,98,36,50,52,1,1,0,0,0,0,0,0,25,4,98,36,50,53,1,1,0,0,0,0,0,0,26,4,98,36,50,54,1,1,0,0,0,0,0,0,27,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C72_3words : List Nat := C72_3p0

theorem C72_3wire : C72_3.flatMap columnWords = C72_3words := by
  rfl

theorem C72_3wordBound : C72_3words.all wordBound = true := by
  simp only [C72_3words,List.all_append,C72_3p0bound]
  try rfl

theorem C72_3bounded : ∀ n ∈ C72_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C72_3wordBound

theorem C72_3length : C72_3.length = 4 := by rfl

def M72 : Module := ⟨72, [115,105,103,110,101,100,95,76,84], false, false, C72_0 ++ C72_1 ++ C72_2 ++ C72_3, ((List.range 0).map (fun n => [n]))⟩

def M72prefix : List Nat := [72,9,115,105,103,110,101,100,95,76,84,0,0,0,0,28]
theorem M72prefixwordBound : M72prefix.all wordBound = true := by decide

def M72words : List Nat := M72prefix ++ C72_0words ++ C72_1words ++ C72_2words ++ C72_3words ++ [0]

theorem M72wire : module.encode M72 = M72words := by
  rw [module_fast]
  simp only [M72,moduleWords,List.length_append,List.flatMap_append,C72_0length,C72_1length,C72_2length,C72_3length,C72_0wire,C72_1wire,C72_2wire,C72_3wire]
  rfl

theorem M72wordBound : M72words.all wordBound = true := by
  simp only [M72words,List.all_append,M72prefixwordBound,C72_0wordBound,C72_1wordBound,C72_2wordBound,C72_3wordBound]
  decide

theorem M72bounded : ∀ n ∈ M72words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M72wordBound

end DivRemFV.Replay
