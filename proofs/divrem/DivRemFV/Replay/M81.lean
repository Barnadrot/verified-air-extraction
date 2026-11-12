import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C81_0 : List Column := [⟨0, [97,114,103,49,39,51], (some (16)), true, false, false⟩,⟨1, [97,114,103,49,39,50], (some (16)), true, false, false⟩,⟨2, [97,114,103,49,39,49], (some (16)), true, false, false⟩,⟨3, [97,114,103,49,39,48], (some (16)), true, false, false⟩,⟨4, [97,114,103,50], (some (7)), true, false, false⟩,⟨5, [111,117,116,95,115,104,108,39,51], (some (16)), false, true, false⟩,⟨6, [111,117,116,95,115,104,108,39,50], (some (16)), false, true, false⟩,⟨7, [111,117,116,95,115,104,108,39,49], (some (16)), false, true, false⟩]

def C81_0p0 : List Nat := [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,7,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1]
theorem C81_0p0bound : C81_0p0.all wordBound = true := (by decide : [0,6,97,114,103,49,39,51,1,16,1,0,0,0,0,0,1,6,97,114,103,49,39,50,1,16,1,0,0,0,0,0,2,6,97,114,103,49,39,49,1,16,1,0,0,0,0,0,3,6,97,114,103,49,39,48,1,16,1,0,0,0,0,0,4,4,97,114,103,50,1,7,1,0,0,0,0,0,5,9,111,117,116,95,115,104,108,39,51,1,16,0,0,1,0,0,0,6,9,111,117,116,95,115,104,108,39,50,1,16,0,0,1,0,0,0,7,9,111,117,116,95,115,104,108,39,49,1].all wordBound = true)

def C81_0p1 : List Nat := [16,0,0,1,0,0,0]
theorem C81_0p1bound : C81_0p1.all wordBound = true := (by decide : [16,0,0,1,0,0,0].all wordBound = true)

def C81_0words : List Nat := C81_0p0 ++ C81_0p1

theorem C81_0wire : C81_0.flatMap columnWords = C81_0words := by
  rfl

theorem C81_0wordBound : C81_0words.all wordBound = true := by
  simp only [C81_0words,List.all_append,C81_0p0bound,C81_0p1bound]
  try rfl

theorem C81_0bounded : ∀ n ∈ C81_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C81_0wordBound

theorem C81_0length : C81_0.length = 8 := by rfl

def C81_1 : List Column := [⟨8, [111,117,116,95,115,104,108,39,48], (some (16)), false, true, false⟩,⟨9, [111,117,116,95,115,104,114,39,51], (some (16)), false, true, false⟩,⟨10, [111,117,116,95,115,104,114,39,50], (some (16)), false, true, false⟩,⟨11, [111,117,116,95,115,104,114,39,49], (some (16)), false, true, false⟩,⟨12, [111,117,116,95,115,104,114,39,48], (some (16)), false, true, false⟩,⟨13, [36,118,108,111,119,48], (some (6)), false, false, false⟩,⟨14, [36,118,104,105,103,104,49], (some (1)), false, false, false⟩,⟨15, [36,114,101,116], (some (1)), false, false, false⟩]

def C81_1p0 : List Nat := [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,118,108,111,119,48,1,6,0,0,0,0,0,0,14,7,36,118,104,105,103,104,49,1,1,0,0,0,0,0,0]
theorem C81_1p0bound : C81_1p0.all wordBound = true := (by decide : [8,9,111,117,116,95,115,104,108,39,48,1,16,0,0,1,0,0,0,9,9,111,117,116,95,115,104,114,39,51,1,16,0,0,1,0,0,0,10,9,111,117,116,95,115,104,114,39,50,1,16,0,0,1,0,0,0,11,9,111,117,116,95,115,104,114,39,49,1,16,0,0,1,0,0,0,12,9,111,117,116,95,115,104,114,39,48,1,16,0,0,1,0,0,0,13,6,36,118,108,111,119,48,1,6,0,0,0,0,0,0,14,7,36,118,104,105,103,104,49,1,1,0,0,0,0,0,0].all wordBound = true)

def C81_1p1 : List Nat := [15,4,36,114,101,116,1,1,0,0,0,0,0,0]
theorem C81_1p1bound : C81_1p1.all wordBound = true := (by decide : [15,4,36,114,101,116,1,1,0,0,0,0,0,0].all wordBound = true)

def C81_1words : List Nat := C81_1p0 ++ C81_1p1

theorem C81_1wire : C81_1.flatMap columnWords = C81_1words := by
  rfl

theorem C81_1wordBound : C81_1words.all wordBound = true := by
  simp only [C81_1words,List.all_append,C81_1p0bound,C81_1p1bound]
  try rfl

theorem C81_1bounded : ∀ n ∈ C81_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C81_1wordBound

theorem C81_1length : C81_1.length = 8 := by rfl

def C81_2 : List Column := [⟨16, [36,108,111,111,107,117,112,95,115,101,108,95,49,54], (some (1)), false, false, false⟩]

def C81_2p0 : List Nat := [16,14,36,108,111,111,107,117,112,95,115,101,108,95,49,54,1,1,0,0,0,0,0,0]
theorem C81_2p0bound : C81_2p0.all wordBound = true := (by decide : [16,14,36,108,111,111,107,117,112,95,115,101,108,95,49,54,1,1,0,0,0,0,0,0].all wordBound = true)

def C81_2words : List Nat := C81_2p0

theorem C81_2wire : C81_2.flatMap columnWords = C81_2words := by
  rfl

theorem C81_2wordBound : C81_2words.all wordBound = true := by
  simp only [C81_2words,List.all_append,C81_2p0bound]
  try rfl

theorem C81_2bounded : ∀ n ∈ C81_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C81_2wordBound

theorem C81_2length : C81_2.length = 1 := by rfl

def M81 : Module := ⟨81, [36,98,105,116,95,115,104,102,95,117,54,52,95,117,55], false, false, C81_0 ++ C81_1 ++ C81_2, ((List.range 0).map (fun n => [n]))⟩

def M81prefix : List Nat := [81,15,36,98,105,116,95,115,104,102,95,117,54,52,95,117,55,0,0,0,0,17]
theorem M81prefixwordBound : M81prefix.all wordBound = true := by decide

def M81words : List Nat := M81prefix ++ C81_0words ++ C81_1words ++ C81_2words ++ [0]

theorem M81wire : module.encode M81 = M81words := by
  rw [module_fast]
  simp only [M81,moduleWords,List.length_append,List.flatMap_append,C81_0length,C81_1length,C81_2length,C81_0wire,C81_1wire,C81_2wire]
  rfl

theorem M81wordBound : M81words.all wordBound = true := by
  simp only [M81words,List.all_append,M81prefixwordBound,C81_0wordBound,C81_1wordBound,C81_2wordBound]
  decide

theorem M81bounded : ∀ n ∈ M81words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M81wordBound

end DivRemFV.Replay
