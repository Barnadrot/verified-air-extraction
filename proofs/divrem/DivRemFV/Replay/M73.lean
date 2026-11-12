import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C73_0 : List Column := [⟨0, [97,39,51], (some (16)), true, false, false⟩,⟨1, [97,39,50], (some (16)), true, false, false⟩,⟨2, [97,39,49], (some (16)), true, false, false⟩,⟨3, [97,39,48], (some (16)), true, false, false⟩,⟨4, [98,39,51], (some (16)), true, false, false⟩,⟨5, [98,39,50], (some (16)), true, false, false⟩,⟨6, [98,39,49], (some (16)), true, false, false⟩,⟨7, [98,39,48], (some (16)), true, false, false⟩]

def C73_0p0 : List Nat := [0,3,97,39,51,1,16,1,0,0,0,0,0,1,3,97,39,50,1,16,1,0,0,0,0,0,2,3,97,39,49,1,16,1,0,0,0,0,0,3,3,97,39,48,1,16,1,0,0,0,0,0,4,3,98,39,51,1,16,1,0,0,0,0,0,5,3,98,39,50,1,16,1,0,0,0,0,0,6,3,98,39,49,1,16,1,0,0,0,0,0,7,3,98,39,48,1,16,1,0,0,0,0,0]
theorem C73_0p0bound : C73_0p0.all wordBound = true := (by decide : [0,3,97,39,51,1,16,1,0,0,0,0,0,1,3,97,39,50,1,16,1,0,0,0,0,0,2,3,97,39,49,1,16,1,0,0,0,0,0,3,3,97,39,48,1,16,1,0,0,0,0,0,4,3,98,39,51,1,16,1,0,0,0,0,0,5,3,98,39,50,1,16,1,0,0,0,0,0,6,3,98,39,49,1,16,1,0,0,0,0,0,7,3,98,39,48,1,16,1,0,0,0,0,0].all wordBound = true)

def C73_0words : List Nat := C73_0p0

theorem C73_0wire : C73_0.flatMap columnWords = C73_0words := by
  rfl

theorem C73_0wordBound : C73_0words.all wordBound = true := by
  simp only [C73_0words,List.all_append,C73_0p0bound]
  try rfl

theorem C73_0bounded : ∀ n ∈ C73_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C73_0wordBound

theorem C73_0length : C73_0.length = 8 := by rfl

def C73_1 : List Column := [⟨8, [99,39,51], (some (16)), false, true, false⟩,⟨9, [99,39,50], (some (16)), false, true, false⟩,⟨10, [99,39,49], (some (16)), false, true, false⟩,⟨11, [99,39,48], (some (16)), false, true, false⟩,⟨12, [36,51,39,52], (some (1)), false, false, false⟩,⟨13, [36,51,39,51], (some (16)), false, false, false⟩,⟨14, [36,51,39,50], (some (16)), false, false, false⟩,⟨15, [36,51,39,49], (some (16)), false, false, false⟩]

def C73_1p0 : List Nat := [8,3,99,39,51,1,16,0,0,1,0,0,0,9,3,99,39,50,1,16,0,0,1,0,0,0,10,3,99,39,49,1,16,0,0,1,0,0,0,11,3,99,39,48,1,16,0,0,1,0,0,0,12,4,36,51,39,52,1,1,0,0,0,0,0,0,13,4,36,51,39,51,1,16,0,0,0,0,0,0,14,4,36,51,39,50,1,16,0,0,0,0,0,0,15,4,36,51,39,49,1,16,0,0,0,0,0,0]
theorem C73_1p0bound : C73_1p0.all wordBound = true := (by decide : [8,3,99,39,51,1,16,0,0,1,0,0,0,9,3,99,39,50,1,16,0,0,1,0,0,0,10,3,99,39,49,1,16,0,0,1,0,0,0,11,3,99,39,48,1,16,0,0,1,0,0,0,12,4,36,51,39,52,1,1,0,0,0,0,0,0,13,4,36,51,39,51,1,16,0,0,0,0,0,0,14,4,36,51,39,50,1,16,0,0,0,0,0,0,15,4,36,51,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C73_1words : List Nat := C73_1p0

theorem C73_1wire : C73_1.flatMap columnWords = C73_1words := by
  rfl

theorem C73_1wordBound : C73_1words.all wordBound = true := by
  simp only [C73_1words,List.all_append,C73_1p0bound]
  try rfl

theorem C73_1bounded : ∀ n ∈ C73_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C73_1wordBound

theorem C73_1length : C73_1.length = 8 := by rfl

def C73_2 : List Column := [⟨16, [36,51,39,48], (some (16)), false, false, false⟩,⟨17, [36,52,39,52], (some (1)), false, false, false⟩,⟨18, [36,52,39,51], (some (16)), false, false, false⟩,⟨19, [36,52,39,50], (some (16)), false, false, false⟩,⟨20, [36,52,39,49], (some (16)), false, false, false⟩,⟨21, [36,52,39,48], (some (16)), false, false, false⟩,⟨22, [99,36,50,50], (some (1)), false, false, false⟩,⟨23, [99,36,50,51], (some (1)), false, false, false⟩]

def C73_2p0 : List Nat := [16,4,36,51,39,48,1,16,0,0,0,0,0,0,17,4,36,52,39,52,1,1,0,0,0,0,0,0,18,4,36,52,39,51,1,16,0,0,0,0,0,0,19,4,36,52,39,50,1,16,0,0,0,0,0,0,20,4,36,52,39,49,1,16,0,0,0,0,0,0,21,4,36,52,39,48,1,16,0,0,0,0,0,0,22,4,99,36,50,50,1,1,0,0,0,0,0,0,23,4,99,36,50,51,1,1,0,0,0,0,0,0]
theorem C73_2p0bound : C73_2p0.all wordBound = true := (by decide : [16,4,36,51,39,48,1,16,0,0,0,0,0,0,17,4,36,52,39,52,1,1,0,0,0,0,0,0,18,4,36,52,39,51,1,16,0,0,0,0,0,0,19,4,36,52,39,50,1,16,0,0,0,0,0,0,20,4,36,52,39,49,1,16,0,0,0,0,0,0,21,4,36,52,39,48,1,16,0,0,0,0,0,0,22,4,99,36,50,50,1,1,0,0,0,0,0,0,23,4,99,36,50,51,1,1,0,0,0,0,0,0].all wordBound = true)

def C73_2words : List Nat := C73_2p0

theorem C73_2wire : C73_2.flatMap columnWords = C73_2words := by
  rfl

theorem C73_2wordBound : C73_2words.all wordBound = true := by
  simp only [C73_2words,List.all_append,C73_2p0bound]
  try rfl

theorem C73_2bounded : ∀ n ∈ C73_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C73_2wordBound

theorem C73_2length : C73_2.length = 8 := by rfl

def C73_3 : List Column := [⟨24, [99,36,50,52], (some (1)), false, false, false⟩,⟨25, [99,36,50,53], (some (1)), false, false, false⟩,⟨26, [36,99,115,116,95,48], (some (0)), false, false, false⟩,⟨27, [36,114,101,116], (some (1)), false, false, false⟩]

def C73_3p0 : List Nat := [24,4,99,36,50,52,1,1,0,0,0,0,0,0,25,4,99,36,50,53,1,1,0,0,0,0,0,0,26,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,27,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C73_3p0bound : C73_3p0.all wordBound = true := (by decide : [24,4,99,36,50,52,1,1,0,0,0,0,0,0,25,4,99,36,50,53,1,1,0,0,0,0,0,0,26,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,27,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C73_3words : List Nat := C73_3p0

theorem C73_3wire : C73_3.flatMap columnWords = C73_3words := by
  rfl

theorem C73_3wordBound : C73_3words.all wordBound = true := by
  simp only [C73_3words,List.all_append,C73_3p0bound]
  try rfl

theorem C73_3bounded : ∀ n ∈ C73_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C73_3wordBound

theorem C73_3length : C73_3.length = 4 := by rfl

def M73 : Module := ⟨73, [115,105,103,110,101,100,95,115,117,109,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100], false, false, C73_0 ++ C73_1 ++ C73_2 ++ C73_3, ((List.range 0).map (fun n => [n]))⟩

def M73prefix : List Nat := [73,25,115,105,103,110,101,100,95,115,117,109,95,111,102,95,100,111,117,98,108,101,95,119,111,114,100,0,0,0,0,28]
theorem M73prefixwordBound : M73prefix.all wordBound = true := by decide

def M73words : List Nat := M73prefix ++ C73_0words ++ C73_1words ++ C73_2words ++ C73_3words ++ [0]

theorem M73wire : module.encode M73 = M73words := by
  rw [module_fast]
  simp only [M73,moduleWords,List.length_append,List.flatMap_append,C73_0length,C73_1length,C73_2length,C73_3length,C73_0wire,C73_1wire,C73_2wire,C73_3wire]
  rfl

theorem M73wordBound : M73words.all wordBound = true := by
  simp only [M73words,List.all_append,M73prefixwordBound,C73_0wordBound,C73_1wordBound,C73_2wordBound,C73_3wordBound]
  decide

theorem M73bounded : ∀ n ∈ M73words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M73wordBound

end DivRemFV.Replay
