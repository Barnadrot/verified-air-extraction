import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C23_0 : List Column := [⟨0, [119,111,114,100,39,51], (some (16)), true, false, false⟩,⟨1, [119,111,114,100,39,50], (some (16)), true, false, false⟩,⟨2, [119,111,114,100,39,49], (some (16)), true, false, false⟩,⟨3, [119,111,114,100,39,48], (some (16)), true, false, false⟩,⟨4, [110], (some (6)), true, false, false⟩,⟨5, [114,101,115,39,51], (some (16)), false, true, false⟩,⟨6, [114,101,115,39,50], (some (16)), false, true, false⟩,⟨7, [114,101,115,39,49], (some (16)), false, true, false⟩]

def C23_0p0 : List Nat := [0,6,119,111,114,100,39,51,1,16,1,0,0,0,0,0,1,6,119,111,114,100,39,50,1,16,1,0,0,0,0,0,2,6,119,111,114,100,39,49,1,16,1,0,0,0,0,0,3,6,119,111,114,100,39,48,1,16,1,0,0,0,0,0,4,1,110,1,6,1,0,0,0,0,0,5,5,114,101,115,39,51,1,16,0,0,1,0,0,0,6,5,114,101,115,39,50,1,16,0,0,1,0,0,0,7,5,114,101,115,39,49,1,16,0,0,1,0,0,0]
theorem C23_0p0bound : C23_0p0.all wordBound = true := (by decide : [0,6,119,111,114,100,39,51,1,16,1,0,0,0,0,0,1,6,119,111,114,100,39,50,1,16,1,0,0,0,0,0,2,6,119,111,114,100,39,49,1,16,1,0,0,0,0,0,3,6,119,111,114,100,39,48,1,16,1,0,0,0,0,0,4,1,110,1,6,1,0,0,0,0,0,5,5,114,101,115,39,51,1,16,0,0,1,0,0,0,6,5,114,101,115,39,50,1,16,0,0,1,0,0,0,7,5,114,101,115,39,49,1,16,0,0,1,0,0,0].all wordBound = true)

def C23_0words : List Nat := C23_0p0

theorem C23_0wire : C23_0.flatMap columnWords = C23_0words := by
  rfl

theorem C23_0wordBound : C23_0words.all wordBound = true := by
  simp only [C23_0words,List.all_append,C23_0p0bound]
  try rfl

theorem C23_0bounded : ∀ n ∈ C23_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C23_0wordBound

theorem C23_0length : C23_0.length = 8 := by rfl

def C23_1 : List Column := [⟨8, [114,101,115,39,48], (some (16)), false, true, false⟩,⟨9, [115,104,105,102,116], (some (7)), false, false, false⟩,⟨10, [36,52], (some (7)), false, false, false⟩,⟨11, [36,53,39,51], (some (16)), false, false, false⟩,⟨12, [36,53,39,50], (some (16)), false, false, false⟩,⟨13, [36,53,39,49], (some (16)), false, false, false⟩,⟨14, [36,53,39,48], (some (16)), false, false, false⟩,⟨15, [36,54,39,51], (some (16)), false, false, false⟩]

def C23_1p0 : List Nat := [8,5,114,101,115,39,48,1,16,0,0,1,0,0,0,9,5,115,104,105,102,116,1,7,0,0,0,0,0,0,10,2,36,52,1,7,0,0,0,0,0,0,11,4,36,53,39,51,1,16,0,0,0,0,0,0,12,4,36,53,39,50,1,16,0,0,0,0,0,0,13,4,36,53,39,49,1,16,0,0,0,0,0,0,14,4,36,53,39,48,1,16,0,0,0,0,0,0,15,4,36,54,39,51,1,16,0,0,0,0,0,0]
theorem C23_1p0bound : C23_1p0.all wordBound = true := (by decide : [8,5,114,101,115,39,48,1,16,0,0,1,0,0,0,9,5,115,104,105,102,116,1,7,0,0,0,0,0,0,10,2,36,52,1,7,0,0,0,0,0,0,11,4,36,53,39,51,1,16,0,0,0,0,0,0,12,4,36,53,39,50,1,16,0,0,0,0,0,0,13,4,36,53,39,49,1,16,0,0,0,0,0,0,14,4,36,53,39,48,1,16,0,0,0,0,0,0,15,4,36,54,39,51,1,16,0,0,0,0,0,0].all wordBound = true)

def C23_1words : List Nat := C23_1p0

theorem C23_1wire : C23_1.flatMap columnWords = C23_1words := by
  rfl

theorem C23_1wordBound : C23_1words.all wordBound = true := by
  simp only [C23_1words,List.all_append,C23_1p0bound]
  try rfl

theorem C23_1bounded : ∀ n ∈ C23_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C23_1wordBound

theorem C23_1length : C23_1.length = 8 := by rfl

def C23_2 : List Column := [⟨16, [36,54,39,50], (some (16)), false, false, false⟩,⟨17, [36,54,39,49], (some (16)), false, false, false⟩,⟨18, [36,54,39,48], (some (16)), false, false, false⟩,⟨19, [36,114,101,116], (some (1)), false, false, false⟩]

def C23_2p0 : List Nat := [16,4,36,54,39,50,1,16,0,0,0,0,0,0,17,4,36,54,39,49,1,16,0,0,0,0,0,0,18,4,36,54,39,48,1,16,0,0,0,0,0,0,19,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C23_2p0bound : C23_2p0.all wordBound = true := (by decide : [16,4,36,54,39,50,1,16,0,0,0,0,0,0,17,4,36,54,39,49,1,16,0,0,0,0,0,0,18,4,36,54,39,48,1,16,0,0,0,0,0,0,19,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C23_2words : List Nat := C23_2p0

theorem C23_2wire : C23_2.flatMap columnWords = C23_2words := by
  rfl

theorem C23_2wordBound : C23_2words.all wordBound = true := by
  simp only [C23_2words,List.all_append,C23_2p0bound]
  try rfl

theorem C23_2bounded : ∀ n ∈ C23_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C23_2wordBound

theorem C23_2length : C23_2.length = 4 := by rfl

def M23 : Module := ⟨23, [98,105,116,95,114,111,116,108,54,52], false, false, C23_0 ++ C23_1 ++ C23_2, ((List.range 0).map (fun n => [n]))⟩

def M23prefix : List Nat := [23,10,98,105,116,95,114,111,116,108,54,52,0,0,0,0,20]
theorem M23prefixwordBound : M23prefix.all wordBound = true := by decide

def M23words : List Nat := M23prefix ++ C23_0words ++ C23_1words ++ C23_2words ++ [0]

theorem M23wire : module.encode M23 = M23words := by
  rw [module_fast]
  simp only [M23,moduleWords,List.length_append,List.flatMap_append,C23_0length,C23_1length,C23_2length,C23_0wire,C23_1wire,C23_2wire]
  rfl

theorem M23wordBound : M23words.all wordBound = true := by
  simp only [M23words,List.all_append,M23prefixwordBound,C23_0wordBound,C23_1wordBound,C23_2wordBound]
  decide

theorem M23bounded : ∀ n ∈ M23words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M23wordBound

end DivRemFV.Replay
