import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C66_0 : List Column := [⟨0, [97,39,49], (some (16)), true, false, false⟩,⟨1, [97,39,48], (some (16)), true, false, false⟩,⟨2, [97,95,110,101,103,39,49], (some (16)), false, true, false⟩,⟨3, [97,95,110,101,103,39,48], (some (16)), false, true, false⟩,⟨4, [97,95,115,105,103,110], (some (1)), false, false, false⟩,⟨5, [36,51,39,49], (some (16)), false, false, false⟩,⟨6, [36,51,39,48], (some (16)), false, false, false⟩,⟨7, [36,52,39,49], (some (16)), false, false, false⟩]

def C66_0p0 : List Nat := [0,3,97,39,49,1,16,1,0,0,0,0,0,1,3,97,39,48,1,16,1,0,0,0,0,0,2,7,97,95,110,101,103,39,49,1,16,0,0,1,0,0,0,3,7,97,95,110,101,103,39,48,1,16,0,0,1,0,0,0,4,6,97,95,115,105,103,110,1,1,0,0,0,0,0,0,5,4,36,51,39,49,1,16,0,0,0,0,0,0,6,4,36,51,39,48,1,16,0,0,0,0,0,0,7,4,36,52,39,49,1,16,0,0,0,0,0,0]
theorem C66_0p0bound : C66_0p0.all wordBound = true := (by decide : [0,3,97,39,49,1,16,1,0,0,0,0,0,1,3,97,39,48,1,16,1,0,0,0,0,0,2,7,97,95,110,101,103,39,49,1,16,0,0,1,0,0,0,3,7,97,95,110,101,103,39,48,1,16,0,0,1,0,0,0,4,6,97,95,115,105,103,110,1,1,0,0,0,0,0,0,5,4,36,51,39,49,1,16,0,0,0,0,0,0,6,4,36,51,39,48,1,16,0,0,0,0,0,0,7,4,36,52,39,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C66_0words : List Nat := C66_0p0

theorem C66_0wire : C66_0.flatMap columnWords = C66_0words := by
  rfl

theorem C66_0wordBound : C66_0words.all wordBound = true := by
  simp only [C66_0words,List.all_append,C66_0p0bound]
  try rfl

theorem C66_0bounded : ∀ n ∈ C66_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C66_0wordBound

theorem C66_0length : C66_0.length = 8 := by rfl

def C66_1 : List Column := [⟨8, [36,52,39,48], (some (16)), false, false, false⟩,⟨9, [115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,55,39,49], (some (15)), false, false, false⟩,⟨10, [115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,55,39,48], (some (16)), false, false, false⟩,⟨11, [102,115,99,36,56], (some (1)), false, false, false⟩,⟨12, [98,36,49,54], (some (1)), false, false, false⟩,⟨13, [98,36,49,55], (some (1)), false, false, false⟩,⟨14, [36,114,101,116], (some (1)), false, false, false⟩,⟨15, [40,105,110,118,32,40,43,32,110,101,103,97,116,105,118,101,95,111,102,95,119,111,114,100,58,97,39,49,32,110,101,103,97,116,105,118,101,95,111,102,95,119,111,114,100,58,97,39,48,41,41], none, false, false, true⟩]

def C66_1p0 : List Nat := [8,4,36,52,39,48,1,16,0,0,0,0,0,0,9,29,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,55,39,49,1,15,0,0,0,0,0,0,10,29,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,55,39,48,1,16,0,0,0,0,0,0,11,5,102,115,99,36,56,1,1,0,0,0,0,0,0,12,4,98,36,49,54,1,1,0,0,0,0,0,0,13,4,98,36,49,55,1]
theorem C66_1p0bound : C66_1p0.all wordBound = true := (by decide : [8,4,36,52,39,48,1,16,0,0,0,0,0,0,9,29,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,55,39,49,1,15,0,0,0,0,0,0,10,29,115,105,103,110,95,98,105,116,95,111,102,95,119,111,114,100,95,97,95,115,117,102,102,105,120,36,55,39,48,1,16,0,0,0,0,0,0,11,5,102,115,99,36,56,1,1,0,0,0,0,0,0,12,4,98,36,49,54,1,1,0,0,0,0,0,0,13,4,98,36,49,55,1].all wordBound = true)

def C66_1p1 : List Nat := [1,0,0,0,0,0,0,14,4,36,114,101,116,1,1,0,0,0,0,0,0,15,51,40,105,110,118,32,40,43,32,110,101,103,97,116,105,118,101,95,111,102,95,119,111,114,100,58,97,39,49,32,110,101,103,97,116,105,118,101,95,111,102,95,119,111,114,100,58,97,39,48,41,41,0,0,0,0,0,0,1,0]
theorem C66_1p1bound : C66_1p1.all wordBound = true := (by decide : [1,0,0,0,0,0,0,14,4,36,114,101,116,1,1,0,0,0,0,0,0,15,51,40,105,110,118,32,40,43,32,110,101,103,97,116,105,118,101,95,111,102,95,119,111,114,100,58,97,39,49,32,110,101,103,97,116,105,118,101,95,111,102,95,119,111,114,100,58,97,39,48,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C66_1words : List Nat := C66_1p0 ++ C66_1p1

theorem C66_1wire : C66_1.flatMap columnWords = C66_1words := by
  rfl

theorem C66_1wordBound : C66_1words.all wordBound = true := by
  simp only [C66_1words,List.all_append,C66_1p0bound,C66_1p1bound]
  try rfl

theorem C66_1bounded : ∀ n ∈ C66_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C66_1wordBound

theorem C66_1length : C66_1.length = 8 := by rfl

def M66 : Module := ⟨66, [110,101,103,97,116,105,118,101,95,111,102,95,119,111,114,100], false, false, C66_0 ++ C66_1, ((List.range 0).map (fun n => [n]))⟩

def M66prefix : List Nat := [66,16,110,101,103,97,116,105,118,101,95,111,102,95,119,111,114,100,0,0,0,0,16]
theorem M66prefixwordBound : M66prefix.all wordBound = true := by decide

def M66words : List Nat := M66prefix ++ C66_0words ++ C66_1words ++ [0]

theorem M66wire : module.encode M66 = M66words := by
  rw [module_fast]
  simp only [M66,moduleWords,List.length_append,List.flatMap_append,C66_0length,C66_1length,C66_0wire,C66_1wire]
  rfl

theorem M66wordBound : M66words.all wordBound = true := by
  simp only [M66words,List.all_append,M66prefixwordBound,C66_0wordBound,C66_1wordBound]
  decide

theorem M66bounded : ∀ n ∈ M66words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M66wordBound

end DivRemFV.Replay
