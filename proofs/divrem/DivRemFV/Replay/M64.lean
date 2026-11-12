import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C64_0 : List Column := [⟨0, [97,39,49], (some (16)), true, false, false⟩,⟨1, [97,39,48], (some (16)), true, false, false⟩,⟨2, [98,39,49], (some (16)), true, false, false⟩,⟨3, [98,39,48], (some (16)), true, false, false⟩,⟨4, [113,39,49], (some (16)), false, true, false⟩,⟨5, [113,39,48], (some (16)), false, true, false⟩,⟨6, [114,39,49], (some (16)), false, true, false⟩,⟨7, [114,39,48], (some (16)), false, true, false⟩]

def C64_0p0 : List Nat := [0,3,97,39,49,1,16,1,0,0,0,0,0,1,3,97,39,48,1,16,1,0,0,0,0,0,2,3,98,39,49,1,16,1,0,0,0,0,0,3,3,98,39,48,1,16,1,0,0,0,0,0,4,3,113,39,49,1,16,0,0,1,0,0,0,5,3,113,39,48,1,16,0,0,1,0,0,0,6,3,114,39,49,1,16,0,0,1,0,0,0,7,3,114,39,48,1,16,0,0,1,0,0,0]
theorem C64_0p0bound : C64_0p0.all wordBound = true := (by decide : [0,3,97,39,49,1,16,1,0,0,0,0,0,1,3,97,39,48,1,16,1,0,0,0,0,0,2,3,98,39,49,1,16,1,0,0,0,0,0,3,3,98,39,48,1,16,1,0,0,0,0,0,4,3,113,39,49,1,16,0,0,1,0,0,0,5,3,113,39,48,1,16,0,0,1,0,0,0,6,3,114,39,49,1,16,0,0,1,0,0,0,7,3,114,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C64_0words : List Nat := C64_0p0

theorem C64_0wire : C64_0.flatMap columnWords = C64_0words := by
  rfl

theorem C64_0wordBound : C64_0words.all wordBound = true := by
  simp only [C64_0words,List.all_append,C64_0p0bound]
  try rfl

theorem C64_0bounded : ∀ n ∈ C64_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C64_0wordBound

theorem C64_0length : C64_0.length = 8 := by rfl

def C64_1 : List Column := [⟨8, [113,95,117,39,49], (some (16)), false, false, false⟩,⟨9, [113,95,117,39,48], (some (16)), false, false, false⟩,⟨10, [114,95,117,39,49], (some (16)), false, false, false⟩,⟨11, [114,95,117,39,48], (some (16)), false, false, false⟩,⟨12, [97,95,115,105,103,110], (some (1)), false, false, false⟩,⟨13, [36,55,39,49], (some (16)), false, false, false⟩,⟨14, [36,55,39,48], (some (16)), false, false, false⟩,⟨15, [36,56,39,49], (some (16)), false, false, false⟩]

def C64_1p0 : List Nat := [8,5,113,95,117,39,49,1,16,0,0,0,0,0,0,9,5,113,95,117,39,48,1,16,0,0,0,0,0,0,10,5,114,95,117,39,49,1,16,0,0,0,0,0,0,11,5,114,95,117,39,48,1,16,0,0,0,0,0,0,12,6,97,95,115,105,103,110,1,1,0,0,0,0,0,0,13,4,36,55,39,49,1,16,0,0,0,0,0,0,14,4,36,55,39,48,1,16,0,0,0,0,0,0,15,4,36,56,39,49,1,16,0,0,0,0,0,0]
theorem C64_1p0bound : C64_1p0.all wordBound = true := (by decide : [8,5,113,95,117,39,49,1,16,0,0,0,0,0,0,9,5,113,95,117,39,48,1,16,0,0,0,0,0,0,10,5,114,95,117,39,49,1,16,0,0,0,0,0,0,11,5,114,95,117,39,48,1,16,0,0,0,0,0,0,12,6,97,95,115,105,103,110,1,1,0,0,0,0,0,0,13,4,36,55,39,49,1,16,0,0,0,0,0,0,14,4,36,55,39,48,1,16,0,0,0,0,0,0,15,4,36,56,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C64_1words : List Nat := C64_1p0

theorem C64_1wire : C64_1.flatMap columnWords = C64_1words := by
  rfl

theorem C64_1wordBound : C64_1words.all wordBound = true := by
  simp only [C64_1words,List.all_append,C64_1p0bound]
  try rfl

theorem C64_1bounded : ∀ n ∈ C64_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C64_1wordBound

theorem C64_1length : C64_1.length = 8 := by rfl

def C64_2 : List Column := [⟨16, [36,56,39,48], (some (16)), false, false, false⟩,⟨17, [36,57], (some (1)), false, false, false⟩,⟨18, [115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,48,39,49], (some (15)), false, false, false⟩,⟨19, [115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,48,39,48], (some (16)), false, false, false⟩,⟨20, [115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,49,39,49], (some (15)), false, false, false⟩,⟨21, [115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,49,39,48], (some (16)), false, false, false⟩,⟨22, [102,115,99,36,49,50], (some (1)), false, false, false⟩,⟨23, [36,114,101,116], (some (1)), false, false, false⟩]

def C64_2p0 : List Nat := [16,4,36,56,39,48,1,16,0,0,0,0,0,0,17,2,36,57,1,1,0,0,0,0,0,0,18,30,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,48,39,49,1,15,0,0,0,0,0,0,19,30,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,48,39,48,1,16,0,0,0,0,0,0,20,30,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115]
theorem C64_2p0bound : C64_2p0.all wordBound = true := (by decide : [16,4,36,56,39,48,1,16,0,0,0,0,0,0,17,2,36,57,1,1,0,0,0,0,0,0,18,30,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,48,39,49,1,15,0,0,0,0,0,0,19,30,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,48,39,48,1,16,0,0,0,0,0,0,20,30,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115].all wordBound = true)

def C64_2p1 : List Nat := [117,102,102,105,120,36,49,49,39,49,1,15,0,0,0,0,0,0,21,30,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,49,39,48,1,16,0,0,0,0,0,0,22,6,102,115,99,36,49,50,1,1,0,0,0,0,0,0,23,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C64_2p1bound : C64_2p1.all wordBound = true := (by decide : [117,102,102,105,120,36,49,49,39,49,1,15,0,0,0,0,0,0,21,30,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,49,49,39,48,1,16,0,0,0,0,0,0,22,6,102,115,99,36,49,50,1,1,0,0,0,0,0,0,23,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C64_2words : List Nat := C64_2p0 ++ C64_2p1

theorem C64_2wire : C64_2.flatMap columnWords = C64_2words := by
  rfl

theorem C64_2wordBound : C64_2words.all wordBound = true := by
  simp only [C64_2words,List.all_append,C64_2p0bound,C64_2p1bound]
  try rfl

theorem C64_2bounded : ∀ n ∈ C64_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C64_2wordBound

theorem C64_2length : C64_2.length = 8 := by rfl

def C64_3 : List Column := [⟨24, [36,108,111,111,107,117,112,95,115,101,108,95,50,52], (some (1)), false, false, false⟩,⟨25, [36,108,111,111,107,117,112,95,115,101,108,95,50,53], (some (1)), false, false, false⟩,⟨26, [40,105,110,118,32,40,43,32,100,105,118,77,111,100,95,51,50,95,115,115,58,98,39,49,32,100,105,118,77,111,100,95,51,50,95,115,115,58,98,39,48,41,41], none, false, false, true⟩]

def C64_3p0 : List Nat := [24,14,36,108,111,111,107,117,112,95,115,101,108,95,50,52,1,1,0,0,0,0,0,0,25,14,36,108,111,111,107,117,112,95,115,101,108,95,50,53,1,1,0,0,0,0,0,0,26,43,40,105,110,118,32,40,43,32,100,105,118,77,111,100,95,51,50,95,115,115,58,98,39,49,32,100,105,118,77,111,100,95,51,50,95,115,115,58,98,39,48,41,41,0,0,0,0,0,0,1,0]
theorem C64_3p0bound : C64_3p0.all wordBound = true := (by decide : [24,14,36,108,111,111,107,117,112,95,115,101,108,95,50,52,1,1,0,0,0,0,0,0,25,14,36,108,111,111,107,117,112,95,115,101,108,95,50,53,1,1,0,0,0,0,0,0,26,43,40,105,110,118,32,40,43,32,100,105,118,77,111,100,95,51,50,95,115,115,58,98,39,49,32,100,105,118,77,111,100,95,51,50,95,115,115,58,98,39,48,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C64_3words : List Nat := C64_3p0

theorem C64_3wire : C64_3.flatMap columnWords = C64_3words := by
  rfl

theorem C64_3wordBound : C64_3words.all wordBound = true := by
  simp only [C64_3words,List.all_append,C64_3p0bound]
  try rfl

theorem C64_3bounded : ∀ n ∈ C64_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C64_3wordBound

theorem C64_3length : C64_3.length = 3 := by rfl

def M64 : Module := ⟨64, [100,105,118,77,111,100,95,51,50,95,115,115], false, false, C64_0 ++ C64_1 ++ C64_2 ++ C64_3, ((List.range 0).map (fun n => [n]))⟩

def M64prefix : List Nat := [64,12,100,105,118,77,111,100,95,51,50,95,115,115,0,0,0,0,27]
theorem M64prefixwordBound : M64prefix.all wordBound = true := by decide

def M64words : List Nat := M64prefix ++ C64_0words ++ C64_1words ++ C64_2words ++ C64_3words ++ [0]

theorem M64wire : module.encode M64 = M64words := by
  rw [module_fast]
  simp only [M64,moduleWords,List.length_append,List.flatMap_append,C64_0length,C64_1length,C64_2length,C64_3length,C64_0wire,C64_1wire,C64_2wire,C64_3wire]
  rfl

theorem M64wordBound : M64words.all wordBound = true := by
  simp only [M64words,List.all_append,M64prefixwordBound,C64_0wordBound,C64_1wordBound,C64_2wordBound,C64_3wordBound]
  decide

theorem M64bounded : ∀ n ∈ M64words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M64wordBound

end DivRemFV.Replay
