import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C71_0 : List Column := [⟨0, [118,97,108,117,101,39,51], (some (16)), true, false, false⟩,⟨1, [118,97,108,117,101,39,50], (some (16)), true, false, false⟩,⟨2, [118,97,108,117,101,39,49], (some (16)), true, false, false⟩,⟨3, [118,97,108,117,101,39,48], (some (16)), true, false, false⟩,⟨4, [115,104,97,109,116], (some (5)), true, false, false⟩,⟨5, [111,117,116,39,49], (some (16)), false, true, false⟩,⟨6, [111,117,116,39,48], (some (16)), false, true, false⟩,⟨7, [119,39,49], (some (16)), false, false, false⟩]

def C71_0p0 : List Nat := [0,7,118,97,108,117,101,39,51,1,16,1,0,0,0,0,0,1,7,118,97,108,117,101,39,50,1,16,1,0,0,0,0,0,2,7,118,97,108,117,101,39,49,1,16,1,0,0,0,0,0,3,7,118,97,108,117,101,39,48,1,16,1,0,0,0,0,0,4,5,115,104,97,109,116,1,5,1,0,0,0,0,0,5,5,111,117,116,39,49,1,16,0,0,1,0,0,0,6,5,111,117,116,39,48,1,16,0,0,1,0,0,0,7,3,119,39,49,1,16,0,0,0,0,0,0]
theorem C71_0p0bound : C71_0p0.all wordBound = true := (by decide : [0,7,118,97,108,117,101,39,51,1,16,1,0,0,0,0,0,1,7,118,97,108,117,101,39,50,1,16,1,0,0,0,0,0,2,7,118,97,108,117,101,39,49,1,16,1,0,0,0,0,0,3,7,118,97,108,117,101,39,48,1,16,1,0,0,0,0,0,4,5,115,104,97,109,116,1,5,1,0,0,0,0,0,5,5,111,117,116,39,49,1,16,0,0,1,0,0,0,6,5,111,117,116,39,48,1,16,0,0,1,0,0,0,7,3,119,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C71_0words : List Nat := C71_0p0

theorem C71_0wire : C71_0.flatMap columnWords = C71_0words := by
  rfl

theorem C71_0wordBound : C71_0words.all wordBound = true := by
  simp only [C71_0words,List.all_append,C71_0p0bound]
  try rfl

theorem C71_0bounded : ∀ n ∈ C71_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C71_0wordBound

theorem C71_0length : C71_0.length = 8 := by rfl

def C71_1 : List Column := [⟨8, [119,39,48], (some (16)), false, false, false⟩,⟨9, [115,105,103,110], (some (1)), false, false, false⟩,⟨10, [108,111,103,105,99,97,108,39,49], (some (16)), false, false, false⟩,⟨11, [108,111,103,105,99,97,108,39,48], (some (16)), false, false, false⟩,⟨12, [109,97,115,107,39,49], (some (16)), false, false, false⟩,⟨13, [109,97,115,107,39,48], (some (16)), false, false, false⟩,⟨14, [36,55,39,49], (some (16)), false, false, false⟩,⟨15, [36,55,39,48], (some (16)), false, false, false⟩]

def C71_1p0 : List Nat := [8,3,119,39,48,1,16,0,0,0,0,0,0,9,4,115,105,103,110,1,1,0,0,0,0,0,0,10,9,108,111,103,105,99,97,108,39,49,1,16,0,0,0,0,0,0,11,9,108,111,103,105,99,97,108,39,48,1,16,0,0,0,0,0,0,12,6,109,97,115,107,39,49,1,16,0,0,0,0,0,0,13,6,109,97,115,107,39,48,1,16,0,0,0,0,0,0,14,4,36,55,39,49,1,16,0,0,0,0,0,0,15,4,36,55,39,48,1,16,0,0,0,0,0,0]
theorem C71_1p0bound : C71_1p0.all wordBound = true := (by decide : [8,3,119,39,48,1,16,0,0,0,0,0,0,9,4,115,105,103,110,1,1,0,0,0,0,0,0,10,9,108,111,103,105,99,97,108,39,49,1,16,0,0,0,0,0,0,11,9,108,111,103,105,99,97,108,39,48,1,16,0,0,0,0,0,0,12,6,109,97,115,107,39,49,1,16,0,0,0,0,0,0,13,6,109,97,115,107,39,48,1,16,0,0,0,0,0,0,14,4,36,55,39,49,1,16,0,0,0,0,0,0,15,4,36,55,39,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C71_1words : List Nat := C71_1p0

theorem C71_1wire : C71_1.flatMap columnWords = C71_1words := by
  rfl

theorem C71_1wordBound : C71_1words.all wordBound = true := by
  simp only [C71_1words,List.all_append,C71_1p0bound]
  try rfl

theorem C71_1bounded : ∀ n ∈ C71_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C71_1wordBound

theorem C71_1length : C71_1.length = 8 := by rfl

def C71_2 : List Column := [⟨16, [36,56,39,49], (some (16)), false, false, false⟩,⟨17, [36,56,39,48], (some (16)), false, false, false⟩,⟨18, [115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,57,39,49], (some (15)), false, false, false⟩,⟨19, [115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,57,39,48], (some (16)), false, false, false⟩,⟨20, [108,98,119,36,49,48,39,49], (some (16)), false, false, false⟩,⟨21, [108,98,119,36,49,48,39,48], (some (16)), false, false, false⟩,⟨22, [36,99,115,116,95,48], (some (0)), false, false, false⟩,⟨23, [98,36,50,51], (some (1)), false, false, false⟩]

def C71_2p0 : List Nat := [16,4,36,56,39,49,1,16,0,0,0,0,0,0,17,4,36,56,39,48,1,16,0,0,0,0,0,0,18,29,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,57,39,49,1,15,0,0,0,0,0,0,19,29,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,57,39,48,1,16,0,0,0,0,0,0,20,8,108,98,119,36,49,48,39,49,1,16,0,0,0,0,0,0,21,8,108,98]
theorem C71_2p0bound : C71_2p0.all wordBound = true := (by decide : [16,4,36,56,39,49,1,16,0,0,0,0,0,0,17,4,36,56,39,48,1,16,0,0,0,0,0,0,18,29,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,57,39,49,1,15,0,0,0,0,0,0,19,29,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,57,39,48,1,16,0,0,0,0,0,0,20,8,108,98,119,36,49,48,39,49,1,16,0,0,0,0,0,0,21,8,108,98].all wordBound = true)

def C71_2p1 : List Nat := [119,36,49,48,39,48,1,16,0,0,0,0,0,0,22,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,23,4,98,36,50,51,1,1,0,0,0,0,0,0]
theorem C71_2p1bound : C71_2p1.all wordBound = true := (by decide : [119,36,49,48,39,48,1,16,0,0,0,0,0,0,22,6,36,99,115,116,95,48,1,0,0,0,0,0,0,0,23,4,98,36,50,51,1,1,0,0,0,0,0,0].all wordBound = true)

def C71_2words : List Nat := C71_2p0 ++ C71_2p1

theorem C71_2wire : C71_2.flatMap columnWords = C71_2words := by
  rfl

theorem C71_2wordBound : C71_2words.all wordBound = true := by
  simp only [C71_2words,List.all_append,C71_2p0bound,C71_2p1bound]
  try rfl

theorem C71_2bounded : ∀ n ∈ C71_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C71_2wordBound

theorem C71_2length : C71_2.length = 8 := by rfl

def C71_3 : List Column := [⟨24, [36,114,101,116], (some (1)), false, false, false⟩,⟨25, [36,108,111,111,107,117,112,95,115,101,108,95,50,53], (some (1)), false, false, false⟩]

def C71_3p0 : List Nat := [24,4,36,114,101,116,1,1,0,0,0,0,0,0,25,14,36,108,111,111,107,117,112,95,115,101,108,95,50,53,1,1,0,0,0,0,0,0]
theorem C71_3p0bound : C71_3p0.all wordBound = true := (by decide : [24,4,36,114,101,116,1,1,0,0,0,0,0,0,25,14,36,108,111,111,107,117,112,95,115,101,108,95,50,53,1,1,0,0,0,0,0,0].all wordBound = true)

def C71_3words : List Nat := C71_3p0

theorem C71_3wire : C71_3.flatMap columnWords = C71_3words := by
  rfl

theorem C71_3wordBound : C71_3words.all wordBound = true := by
  simp only [C71_3words,List.all_append,C71_3p0bound]
  try rfl

theorem C71_3bounded : ∀ n ∈ C71_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C71_3wordBound

theorem C71_3length : C71_3.length = 2 := by rfl

def M71 : Module := ⟨71, [95,97,115,104,114,95,117,51,50], false, false, C71_0 ++ C71_1 ++ C71_2 ++ C71_3, ((List.range 0).map (fun n => [n]))⟩

def M71prefix : List Nat := [71,9,95,97,115,104,114,95,117,51,50,0,0,0,0,26]
theorem M71prefixwordBound : M71prefix.all wordBound = true := by decide

def M71words : List Nat := M71prefix ++ C71_0words ++ C71_1words ++ C71_2words ++ C71_3words ++ [0]

theorem M71wire : module.encode M71 = M71words := by
  rw [module_fast]
  simp only [M71,moduleWords,List.length_append,List.flatMap_append,C71_0length,C71_1length,C71_2length,C71_3length,C71_0wire,C71_1wire,C71_2wire,C71_3wire]
  rfl

theorem M71wordBound : M71words.all wordBound = true := by
  simp only [M71words,List.all_append,M71prefixwordBound,C71_0wordBound,C71_1wordBound,C71_2wordBound,C71_3wordBound]
  decide

theorem M71bounded : ∀ n ∈ M71words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M71wordBound

end DivRemFV.Replay
