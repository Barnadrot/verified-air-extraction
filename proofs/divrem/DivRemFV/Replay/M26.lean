import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C26_0 : List Column := [⟨0, [97,100,100,114,101,115,115], (some (5)), true, false, false⟩,⟨1, [102,101,108,116], none, false, true, true⟩,⟨2, [36,101,120,101,99], (some (1)), false, false, false⟩,⟨3, [36,105,115,95,119,114,105,116,101], (some (1)), false, false, false⟩,⟨4, [36,118,97,108,117,101,95,114,101,97,100,95,48], none, false, false, true⟩,⟨5, [36,116,115,95,119,114,105,116,116,101,110,95,48], (some (16)), false, false, false⟩,⟨6, [36,116,115,95,119,114,105,116,116,101,110,95,49], (some (16)), false, false, false⟩,⟨7, [36,116,115,95,114,101,97,100,95,48], (some (16)), false, false, false⟩]

def C26_0p0 : List Nat := [0,7,97,100,100,114,101,115,115,1,5,1,0,0,0,0,0,1,4,102,101,108,116,0,0,0,0,1,0,1,0,2,5,36,101,120,101,99,1,1,0,0,0,0,0,0,3,9,36,105,115,95,119,114,105,116,101,1,1,0,0,0,0,0,0,4,13,36,118,97,108,117,101,95,114,101,97,100,95,48,0,0,0,0,0,0,1,0,5,13,36,116,115,95,119,114,105,116,116,101,110,95,48,1,16,0,0,0,0,0,0,6,13,36,116,115,95,119,114,105,116,116,101,110,95,49,1,16]
theorem C26_0p0bound : C26_0p0.all wordBound = true := (by decide : [0,7,97,100,100,114,101,115,115,1,5,1,0,0,0,0,0,1,4,102,101,108,116,0,0,0,0,1,0,1,0,2,5,36,101,120,101,99,1,1,0,0,0,0,0,0,3,9,36,105,115,95,119,114,105,116,101,1,1,0,0,0,0,0,0,4,13,36,118,97,108,117,101,95,114,101,97,100,95,48,0,0,0,0,0,0,1,0,5,13,36,116,115,95,119,114,105,116,116,101,110,95,48,1,16,0,0,0,0,0,0,6,13,36,116,115,95,119,114,105,116,116,101,110,95,49,1,16].all wordBound = true)

def C26_0p1 : List Nat := [0,0,0,0,0,0,7,10,36,116,115,95,114,101,97,100,95,48,1,16,0,0,0,0,0,0]
theorem C26_0p1bound : C26_0p1.all wordBound = true := (by decide : [0,0,0,0,0,0,7,10,36,116,115,95,114,101,97,100,95,48,1,16,0,0,0,0,0,0].all wordBound = true)

def C26_0words : List Nat := C26_0p0 ++ C26_0p1

theorem C26_0wire : C26_0.flatMap columnWords = C26_0words := by
  rfl

theorem C26_0wordBound : C26_0words.all wordBound = true := by
  simp only [C26_0words,List.all_append,C26_0p0bound,C26_0p1bound]
  try rfl

theorem C26_0bounded : ∀ n ∈ C26_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C26_0wordBound

theorem C26_0length : C26_0.length = 8 := by rfl

def C26_1 : List Column := [⟨8, [36,116,115,95,114,101,97,100,95,49], (some (16)), false, false, false⟩,⟨9, [36,116,115,95,100,101,108,116,97,95,48], (some (16)), false, false, false⟩,⟨10, [36,116,115,95,100,101,108,116,97,95,49], (some (16)), false, false, false⟩,⟨11, [36,116,115,95,99,97,114,114,121,95,48], (some (1)), false, false, false⟩,⟨12, [36,101,120,101,99,95,119,114,105,116,101], (some (1)), false, false, false⟩,⟨13, [36,101,120,101,99,95,114,101,97,100], (some (1)), false, false, false⟩,⟨14, [36,116,101,109,112,111,114,97,108,95,116,115,95,48], (some (16)), false, false, false⟩,⟨15, [36,116,101,109,112,111,114,97,108,95,116,115,95,49], (some (16)), false, false, false⟩]

def C26_1p0 : List Nat := [8,10,36,116,115,95,114,101,97,100,95,49,1,16,0,0,0,0,0,0,9,11,36,116,115,95,100,101,108,116,97,95,48,1,16,0,0,0,0,0,0,10,11,36,116,115,95,100,101,108,116,97,95,49,1,16,0,0,0,0,0,0,11,11,36,116,115,95,99,97,114,114,121,95,48,1,1,0,0,0,0,0,0,12,11,36,101,120,101,99,95,119,114,105,116,101,1,1,0,0,0,0,0,0,13,10,36,101,120,101,99,95,114,101,97,100,1,1,0,0,0,0,0,0,14,14,36,116]
theorem C26_1p0bound : C26_1p0.all wordBound = true := (by decide : [8,10,36,116,115,95,114,101,97,100,95,49,1,16,0,0,0,0,0,0,9,11,36,116,115,95,100,101,108,116,97,95,48,1,16,0,0,0,0,0,0,10,11,36,116,115,95,100,101,108,116,97,95,49,1,16,0,0,0,0,0,0,11,11,36,116,115,95,99,97,114,114,121,95,48,1,1,0,0,0,0,0,0,12,11,36,101,120,101,99,95,119,114,105,116,101,1,1,0,0,0,0,0,0,13,10,36,101,120,101,99,95,114,101,97,100,1,1,0,0,0,0,0,0,14,14,36,116].all wordBound = true)

def C26_1p1 : List Nat := [101,109,112,111,114,97,108,95,116,115,95,48,1,16,0,0,0,0,0,0,15,14,36,116,101,109,112,111,114,97,108,95,116,115,95,49,1,16,0,0,0,0,0,0]
theorem C26_1p1bound : C26_1p1.all wordBound = true := (by decide : [101,109,112,111,114,97,108,95,116,115,95,48,1,16,0,0,0,0,0,0,15,14,36,116,101,109,112,111,114,97,108,95,116,115,95,49,1,16,0,0,0,0,0,0].all wordBound = true)

def C26_1words : List Nat := C26_1p0 ++ C26_1p1

theorem C26_1wire : C26_1.flatMap columnWords = C26_1words := by
  rfl

theorem C26_1wordBound : C26_1words.all wordBound = true := by
  simp only [C26_1words,List.all_append,C26_1p0bound,C26_1p1bound]
  try rfl

theorem C26_1bounded : ∀ n ∈ C26_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C26_1wordBound

theorem C26_1length : C26_1.length = 8 := by rfl

def C26_2 : List Column := [⟨16, [36,116,101,109,112,111,114,97,108,95,116,115,95,99,97,114,114,121,95,48], (some (1)), false, false, false⟩,⟨17, [40,105,110,118,32,40,43,32,40,45,32,49,32,40,115,104,105,102,116,32,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,58,36,101,120,101,99,32,45,49,41,41,32,40,45,32,49,32,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,58,36,101,120,101,99,41,41,41], none, false, false, true⟩]

def C26_2p0 : List Nat := [16,20,36,116,101,109,112,111,114,97,108,95,116,115,95,99,97,114,114,121,95,48,1,1,0,0,0,0,0,0,17,76,40,105,110,118,32,40,43,32,40,45,32,49,32,40,115,104,105,102,116,32,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,58,36,101,120,101,99,32,45,49,41,41,32,40,45,32,49,32,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,58,36,101,120,101,99,41,41,41,0,0,0,0,0,0,1,0]
theorem C26_2p0bound : C26_2p0.all wordBound = true := (by decide : [16,20,36,116,101,109,112,111,114,97,108,95,116,115,95,99,97,114,114,121,95,48,1,1,0,0,0,0,0,0,17,76,40,105,110,118,32,40,43,32,40,45,32,49,32,40,115,104,105,102,116,32,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,58,36,101,120,101,99,32,45,49,41,41,32,40,45,32,49,32,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,58,36,101,120,101,99,41,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C26_2words : List Nat := C26_2p0

theorem C26_2wire : C26_2.flatMap columnWords = C26_2words := by
  rfl

theorem C26_2wordBound : C26_2words.all wordBound = true := by
  simp only [C26_2words,List.all_append,C26_2p0bound]
  try rfl

theorem C26_2bounded : ∀ n ∈ C26_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C26_2wordBound

theorem C26_2length : C26_2.length = 2 := by rfl

def M26 : Module := ⟨26, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101], false, false, C26_0 ++ C26_1 ++ C26_2, ((List.range 0).map (fun n => [n]))⟩

def M26prefix : List Nat := [26,15,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,0,0,0,0,18]
theorem M26prefixwordBound : M26prefix.all wordBound = true := by decide

def M26words : List Nat := M26prefix ++ C26_0words ++ C26_1words ++ C26_2words ++ [0]

theorem M26wire : module.encode M26 = M26words := by
  rw [module_fast]
  simp only [M26,moduleWords,List.length_append,List.flatMap_append,C26_0length,C26_1length,C26_2length,C26_0wire,C26_1wire,C26_2wire]
  rfl

theorem M26wordBound : M26words.all wordBound = true := by
  simp only [M26words,List.all_append,M26prefixwordBound,C26_0wordBound,C26_1wordBound,C26_2wordBound]
  decide

theorem M26bounded : ∀ n ∈ M26words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M26wordBound

end DivRemFV.Replay
