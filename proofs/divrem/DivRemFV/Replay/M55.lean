import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C55_0 : List Column := [⟨0, [97,39,51], (some (16)), true, false, false⟩,⟨1, [97,39,50], (some (16)), true, false, false⟩,⟨2, [97,39,49], (some (16)), true, false, false⟩,⟨3, [97,39,48], (some (16)), true, false, false⟩,⟨4, [97,98,115,39,51], (some (16)), false, true, false⟩,⟨5, [97,98,115,39,50], (some (16)), false, true, false⟩,⟨6, [97,98,115,39,49], (some (16)), false, true, false⟩,⟨7, [97,98,115,39,48], (some (16)), false, true, false⟩]

def C55_0p0 : List Nat := [0,3,97,39,51,1,16,1,0,0,0,0,0,1,3,97,39,50,1,16,1,0,0,0,0,0,2,3,97,39,49,1,16,1,0,0,0,0,0,3,3,97,39,48,1,16,1,0,0,0,0,0,4,5,97,98,115,39,51,1,16,0,0,1,0,0,0,5,5,97,98,115,39,50,1,16,0,0,1,0,0,0,6,5,97,98,115,39,49,1,16,0,0,1,0,0,0,7,5,97,98,115,39,48,1,16,0,0,1,0,0,0]
theorem C55_0p0bound : C55_0p0.all wordBound = true := (by decide : [0,3,97,39,51,1,16,1,0,0,0,0,0,1,3,97,39,50,1,16,1,0,0,0,0,0,2,3,97,39,49,1,16,1,0,0,0,0,0,3,3,97,39,48,1,16,1,0,0,0,0,0,4,5,97,98,115,39,51,1,16,0,0,1,0,0,0,5,5,97,98,115,39,50,1,16,0,0,1,0,0,0,6,5,97,98,115,39,49,1,16,0,0,1,0,0,0,7,5,97,98,115,39,48,1,16,0,0,1,0,0,0].all wordBound = true)

def C55_0words : List Nat := C55_0p0

theorem C55_0wire : C55_0.flatMap columnWords = C55_0words := by
  rfl

theorem C55_0wordBound : C55_0words.all wordBound = true := by
  simp only [C55_0words,List.all_append,C55_0p0bound]
  try rfl

theorem C55_0bounded : ∀ n ∈ C55_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C55_0wordBound

theorem C55_0length : C55_0.length = 8 := by rfl

def C55_1 : List Column := [⟨8, [97,95,115,105,103,110], (some (1)), false, false, false⟩,⟨9, [36,51,39,51], (some (16)), false, false, false⟩,⟨10, [36,51,39,50], (some (16)), false, false, false⟩,⟨11, [36,51,39,49], (some (16)), false, false, false⟩,⟨12, [36,51,39,48], (some (16)), false, false, false⟩,⟨13, [36,52,39,51], (some (16)), false, false, false⟩,⟨14, [36,52,39,50], (some (16)), false, false, false⟩,⟨15, [36,52,39,49], (some (16)), false, false, false⟩]

def C55_1p0 : List Nat := [8,6,97,95,115,105,103,110,1,1,0,0,0,0,0,0,9,4,36,51,39,51,1,16,0,0,0,0,0,0,10,4,36,51,39,50,1,16,0,0,0,0,0,0,11,4,36,51,39,49,1,16,0,0,0,0,0,0,12,4,36,51,39,48,1,16,0,0,0,0,0,0,13,4,36,52,39,51,1,16,0,0,0,0,0,0,14,4,36,52,39,50,1,16,0,0,0,0,0,0,15,4,36,52,39,49,1,16,0,0,0,0,0,0]
theorem C55_1p0bound : C55_1p0.all wordBound = true := (by decide : [8,6,97,95,115,105,103,110,1,1,0,0,0,0,0,0,9,4,36,51,39,51,1,16,0,0,0,0,0,0,10,4,36,51,39,50,1,16,0,0,0,0,0,0,11,4,36,51,39,49,1,16,0,0,0,0,0,0,12,4,36,51,39,48,1,16,0,0,0,0,0,0,13,4,36,52,39,51,1,16,0,0,0,0,0,0,14,4,36,52,39,50,1,16,0,0,0,0,0,0,15,4,36,52,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C55_1words : List Nat := C55_1p0

theorem C55_1wire : C55_1.flatMap columnWords = C55_1words := by
  rfl

theorem C55_1wordBound : C55_1words.all wordBound = true := by
  simp only [C55_1words,List.all_append,C55_1p0bound]
  try rfl

theorem C55_1bounded : ∀ n ∈ C55_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C55_1wordBound

theorem C55_1length : C55_1.length = 8 := by rfl

def C55_2 : List Column := [⟨16, [36,52,39,48], (some (16)), false, false, false⟩,⟨17, [115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,51], (some (15)), false, false, false⟩,⟨18, [115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,50], (some (16)), false, false, false⟩,⟨19, [115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,49], (some (16)), false, false, false⟩,⟨20, [115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,48], (some (16)), false, false, false⟩,⟨21, [98,36,50,49], (some (1)), false, false, false⟩,⟨22, [98,36,50,50], (some (1)), false, false, false⟩,⟨23, [98,36,50,51], (some (1)), false, false, false⟩]

def C55_2p0 : List Nat := [16,4,36,52,39,48,1,16,0,0,0,0,0,0,17,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,51,1,15,0,0,0,0,0,0,18,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,50,1,16,0,0,0,0,0,0,19,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119]
theorem C55_2p0bound : C55_2p0.all wordBound = true := (by decide : [16,4,36,52,39,48,1,16,0,0,0,0,0,0,17,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,51,1,15,0,0,0,0,0,0,18,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,50,1,16,0,0,0,0,0,0,19,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119].all wordBound = true)

def C55_2p1 : List Nat := [111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,49,1,16,0,0,0,0,0,0,20,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,48,1,16,0,0,0,0,0,0,21,4,98,36,50,49,1,1,0,0,0,0,0,0,22,4,98,36,50,50,1,1,0,0,0,0,0,0,23,4,98,36,50,51,1,1,0,0,0,0,0,0]
theorem C55_2p1bound : C55_2p1.all wordBound = true := (by decide : [111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,49,1,16,0,0,0,0,0,0,20,36,115,105,103,110,95,98,105,116,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,53,39,48,1,16,0,0,0,0,0,0,21,4,98,36,50,49,1,1,0,0,0,0,0,0,22,4,98,36,50,50,1,1,0,0,0,0,0,0,23,4,98,36,50,51,1,1,0,0,0,0,0,0].all wordBound = true)

def C55_2words : List Nat := C55_2p0 ++ C55_2p1

theorem C55_2wire : C55_2.flatMap columnWords = C55_2words := by
  rfl

theorem C55_2wordBound : C55_2words.all wordBound = true := by
  simp only [C55_2words,List.all_append,C55_2p0bound,C55_2p1bound]
  try rfl

theorem C55_2bounded : ∀ n ∈ C55_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C55_2wordBound

theorem C55_2length : C55_2.length = 8 := by rfl

def C55_3 : List Column := [⟨24, [99,36,50,52], (some (1)), false, false, false⟩,⟨25, [99,36,50,53], (some (1)), false, false, false⟩,⟨26, [99,36,50,54], (some (1)), false, false, false⟩,⟨27, [36,114,101,116], (some (1)), false, false, false⟩]

def C55_3p0 : List Nat := [24,4,99,36,50,52,1,1,0,0,0,0,0,0,25,4,99,36,50,53,1,1,0,0,0,0,0,0,26,4,99,36,50,54,1,1,0,0,0,0,0,0,27,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C55_3p0bound : C55_3p0.all wordBound = true := (by decide : [24,4,99,36,50,52,1,1,0,0,0,0,0,0,25,4,99,36,50,53,1,1,0,0,0,0,0,0,26,4,99,36,50,54,1,1,0,0,0,0,0,0,27,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C55_3words : List Nat := C55_3p0

theorem C55_3wire : C55_3.flatMap columnWords = C55_3words := by
  rfl

theorem C55_3wordBound : C55_3words.all wordBound = true := by
  simp only [C55_3words,List.all_append,C55_3p0bound]
  try rfl

theorem C55_3bounded : ∀ n ∈ C55_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C55_3wordBound

theorem C55_3length : C55_3.length = 4 := by rfl

def M55 : Module := ⟨55, [97,98,115,111,108,117,116,101,95,118,97,108,117,101,95,100,111,117,98,108,101,95,119,111,114,100], false, false, C55_0 ++ C55_1 ++ C55_2 ++ C55_3, ((List.range 0).map (fun n => [n]))⟩

def M55prefix : List Nat := [55,26,97,98,115,111,108,117,116,101,95,118,97,108,117,101,95,100,111,117,98,108,101,95,119,111,114,100,0,0,0,0,28]
theorem M55prefixwordBound : M55prefix.all wordBound = true := by decide

def M55words : List Nat := M55prefix ++ C55_0words ++ C55_1words ++ C55_2words ++ C55_3words ++ [0]

theorem M55wire : module.encode M55 = M55words := by
  rw [module_fast]
  simp only [M55,moduleWords,List.length_append,List.flatMap_append,C55_0length,C55_1length,C55_2length,C55_3length,C55_0wire,C55_1wire,C55_2wire,C55_3wire]
  rfl

theorem M55wordBound : M55words.all wordBound = true := by
  simp only [M55words,List.all_append,M55prefixwordBound,C55_0wordBound,C55_1wordBound,C55_2wordBound,C55_3wordBound]
  decide

theorem M55bounded : ∀ n ∈ M55words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M55wordBound

end DivRemFV.Replay
