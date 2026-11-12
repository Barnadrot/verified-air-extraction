import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def C36_0 : List Column := [⟨0, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49], (some (16)), true, false, false⟩,⟨1, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48], (some (16)), true, false, false⟩,⟨2, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49], (some (16)), false, true, false⟩,⟨3, [112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,48], (some (16)), false, true, false⟩,⟨4, [115,117,109], none, false, false, true⟩,⟨5, [105], (some (5)), false, false, false⟩,⟨6, [105,36,49], (some (5)), false, false, false⟩,⟨7, [36,51], none, false, false, true⟩]

def C36_0p0 : List Nat := [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111]
theorem C36_0p0bound : C36_0p0.all wordBound = true := (by decide : [0,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,49,1,16,1,0,0,0,0,0,1,23,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,39,48,1,16,1,0,0,0,0,0,2,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111,117,116,39,49,1,16,0,0,1,0,0,0,3,27,112,111,115,101,105,100,111,110,50,95,115,116,97,116,101,36,115,116,97,109,112,95,111].all wordBound = true)

def C36_0p1 : List Nat := [117,116,39,48,1,16,0,0,1,0,0,0,4,3,115,117,109,0,0,0,0,0,0,1,0,5,1,105,1,5,0,0,0,0,0,0,6,3,105,36,49,1,5,0,0,0,0,0,0,7,2,36,51,0,0,0,0,0,0,1,0]
theorem C36_0p1bound : C36_0p1.all wordBound = true := (by decide : [117,116,39,48,1,16,0,0,1,0,0,0,4,3,115,117,109,0,0,0,0,0,0,1,0,5,1,105,1,5,0,0,0,0,0,0,6,3,105,36,49,1,5,0,0,0,0,0,0,7,2,36,51,0,0,0,0,0,0,1,0].all wordBound = true)

def C36_0words : List Nat := C36_0p0 ++ C36_0p1

theorem C36_0wire : C36_0.flatMap columnWords = C36_0words := by
  rfl

theorem C36_0wordBound : C36_0words.all wordBound = true := by
  simp only [C36_0words,List.all_append,C36_0p0bound,C36_0p1bound]
  try rfl

theorem C36_0bounded : ∀ n ∈ C36_0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C36_0wordBound

theorem C36_0length : C36_0.length = 8 := by rfl

def C36_1 : List Column := [⟨8, [36,52], none, false, false, true⟩,⟨9, [36,53], none, false, false, true⟩,⟨10, [36,54], none, false, false, true⟩,⟨11, [36,55], none, false, false, true⟩,⟨12, [108,99,109,36,56], (some (5)), false, false, false⟩,⟨13, [108,99,109,36,57], (some (1)), false, false, false⟩,⟨14, [108,99,109,36,49,48], (some (5)), false, false, false⟩,⟨15, [108,99,109,36,49,49], (some (1)), false, false, false⟩]

def C36_1p0 : List Nat := [8,2,36,52,0,0,0,0,0,0,1,0,9,2,36,53,0,0,0,0,0,0,1,0,10,2,36,54,0,0,0,0,0,0,1,0,11,2,36,55,0,0,0,0,0,0,1,0,12,5,108,99,109,36,56,1,5,0,0,0,0,0,0,13,5,108,99,109,36,57,1,1,0,0,0,0,0,0,14,6,108,99,109,36,49,48,1,5,0,0,0,0,0,0,15,6,108,99,109,36,49,49,1,1,0,0,0,0,0,0]
theorem C36_1p0bound : C36_1p0.all wordBound = true := (by decide : [8,2,36,52,0,0,0,0,0,0,1,0,9,2,36,53,0,0,0,0,0,0,1,0,10,2,36,54,0,0,0,0,0,0,1,0,11,2,36,55,0,0,0,0,0,0,1,0,12,5,108,99,109,36,56,1,5,0,0,0,0,0,0,13,5,108,99,109,36,57,1,1,0,0,0,0,0,0,14,6,108,99,109,36,49,48,1,5,0,0,0,0,0,0,15,6,108,99,109,36,49,49,1,1,0,0,0,0,0,0].all wordBound = true)

def C36_1words : List Nat := C36_1p0

theorem C36_1wire : C36_1.flatMap columnWords = C36_1words := by
  rfl

theorem C36_1wordBound : C36_1words.all wordBound = true := by
  simp only [C36_1words,List.all_append,C36_1p0bound]
  try rfl

theorem C36_1bounded : ∀ n ∈ C36_1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C36_1wordBound

theorem C36_1length : C36_1.length = 8 := by rfl

def C36_2 : List Column := [⟨16, [115,116,97,109,112,36,49,52,39,49], (some (16)), false, false, false⟩,⟨17, [115,116,97,109,112,36,49,52,39,48], (some (16)), false, false, false⟩,⟨18, [115,116,97,109,112,36,49,54,39,49], (some (16)), false, false, false⟩,⟨19, [115,116,97,109,112,36,49,54,39,48], (some (16)), false, false, false⟩,⟨20, [99,36,50,52], (some (1)), false, false, false⟩,⟨21, [99,36,50,53], (some (1)), false, false, false⟩,⟨22, [99,36,50,56], (some (1)), false, false, false⟩,⟨23, [102,108,97,36,50,51], (some (5)), false, false, false⟩]

def C36_2p0 : List Nat := [16,10,115,116,97,109,112,36,49,52,39,49,1,16,0,0,0,0,0,0,17,10,115,116,97,109,112,36,49,52,39,48,1,16,0,0,0,0,0,0,18,10,115,116,97,109,112,36,49,54,39,49,1,16,0,0,0,0,0,0,19,10,115,116,97,109,112,36,49,54,39,48,1,16,0,0,0,0,0,0,20,4,99,36,50,52,1,1,0,0,0,0,0,0,21,4,99,36,50,53,1,1,0,0,0,0,0,0,22,4,99,36,50,56,1,1,0,0,0,0,0,0,23,6,102,108,97,36]
theorem C36_2p0bound : C36_2p0.all wordBound = true := (by decide : [16,10,115,116,97,109,112,36,49,52,39,49,1,16,0,0,0,0,0,0,17,10,115,116,97,109,112,36,49,52,39,48,1,16,0,0,0,0,0,0,18,10,115,116,97,109,112,36,49,54,39,49,1,16,0,0,0,0,0,0,19,10,115,116,97,109,112,36,49,54,39,48,1,16,0,0,0,0,0,0,20,4,99,36,50,52,1,1,0,0,0,0,0,0,21,4,99,36,50,53,1,1,0,0,0,0,0,0,22,4,99,36,50,56,1,1,0,0,0,0,0,0,23,6,102,108,97,36].all wordBound = true)

def C36_2p1 : List Nat := [50,51,1,5,0,0,0,0,0,0]
theorem C36_2p1bound : C36_2p1.all wordBound = true := (by decide : [50,51,1,5,0,0,0,0,0,0].all wordBound = true)

def C36_2words : List Nat := C36_2p0 ++ C36_2p1

theorem C36_2wire : C36_2.flatMap columnWords = C36_2words := by
  rfl

theorem C36_2wordBound : C36_2words.all wordBound = true := by
  simp only [C36_2words,List.all_append,C36_2p0bound,C36_2p1bound]
  try rfl

theorem C36_2bounded : ∀ n ∈ C36_2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C36_2wordBound

theorem C36_2length : C36_2.length = 8 := by rfl

def C36_3 : List Column := [⟨24, [102,108,97,36,50,52], (some (16)), false, false, false⟩,⟨25, [102,108,97,36,50,53], (some (16)), false, false, false⟩,⟨26, [102,108,97,36,50,54], (some (16)), false, false, false⟩,⟨27, [102,108,97,36,50,55], (some (16)), false, false, false⟩,⟨28, [36,114,101,116], (some (1)), false, false, false⟩,⟨29, [36,112,99], (some (2)), false, false, false⟩,⟨30, [36,105,115,95,112,99,95,49], (some (1)), false, false, false⟩,⟨31, [36,105,115,95,112,99,95,50], (some (1)), false, false, false⟩]

def C36_3p0 : List Nat := [24,6,102,108,97,36,50,52,1,16,0,0,0,0,0,0,25,6,102,108,97,36,50,53,1,16,0,0,0,0,0,0,26,6,102,108,97,36,50,54,1,16,0,0,0,0,0,0,27,6,102,108,97,36,50,55,1,16,0,0,0,0,0,0,28,4,36,114,101,116,1,1,0,0,0,0,0,0,29,3,36,112,99,1,2,0,0,0,0,0,0,30,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,31,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0]
theorem C36_3p0bound : C36_3p0.all wordBound = true := (by decide : [24,6,102,108,97,36,50,52,1,16,0,0,0,0,0,0,25,6,102,108,97,36,50,53,1,16,0,0,0,0,0,0,26,6,102,108,97,36,50,54,1,16,0,0,0,0,0,0,27,6,102,108,97,36,50,55,1,16,0,0,0,0,0,0,28,4,36,114,101,116,1,1,0,0,0,0,0,0,29,3,36,112,99,1,2,0,0,0,0,0,0,30,8,36,105,115,95,112,99,95,49,1,1,0,0,0,0,0,0,31,8,36,105,115,95,112,99,95,50,1,1,0,0,0,0,0,0].all wordBound = true)

def C36_3words : List Nat := C36_3p0

theorem C36_3wire : C36_3.flatMap columnWords = C36_3words := by
  rfl

theorem C36_3wordBound : C36_3words.all wordBound = true := by
  simp only [C36_3words,List.all_append,C36_3p0bound]
  try rfl

theorem C36_3bounded : ∀ n ∈ C36_3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C36_3wordBound

theorem C36_3length : C36_3.length = 8 := by rfl

def C36_4 : List Column := [⟨32, [36,105,115,95,112,99,95,51], (some (1)), false, false, false⟩,⟨33, [36,108,111,111,107,117,112,95,115,101,108,95,51,51], (some (1)), false, false, false⟩,⟨34, [36,108,111,111,107,117,112,95,115,101,108,95,51,52], (some (1)), false, false, false⟩,⟨35, [36,108,111,111,107,117,112,95,115,101,108,95,51,53], (some (1)), false, false, false⟩,⟨36, [40,105,110,118,32,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,58,36,112,99,41], none, false, false, true⟩,⟨37, [40,105,110,118,32,40,43,32,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,58,108,99,109,36,57,32,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,58,108,99,109,36,49,49,41,41], none, false, false, true⟩]

def C36_4p0 : List Nat := [32,8,36,105,115,95,112,99,95,51,1,1,0,0,0,0,0,0,33,14,36,108,111,111,107,117,112,95,115,101,108,95,51,51,1,1,0,0,0,0,0,0,34,14,36,108,111,111,107,117,112,95,115,101,108,95,51,52,1,1,0,0,0,0,0,0,35,14,36,108,111,111,107,117,112,95,115,101,108,95,51,53,1,1,0,0,0,0,0,0,36,26,40,105,110,118,32,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,58,36,112,99,41,0,0,0,0,0,0,1,0,37,56]
theorem C36_4p0bound : C36_4p0.all wordBound = true := (by decide : [32,8,36,105,115,95,112,99,95,51,1,1,0,0,0,0,0,0,33,14,36,108,111,111,107,117,112,95,115,101,108,95,51,51,1,1,0,0,0,0,0,0,34,14,36,108,111,111,107,117,112,95,115,101,108,95,51,52,1,1,0,0,0,0,0,0,35,14,36,108,111,111,107,117,112,95,115,101,108,95,51,53,1,1,0,0,0,0,0,0,36,26,40,105,110,118,32,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,58,36,112,99,41,0,0,0,0,0,0,1,0,37,56].all wordBound = true)

def C36_4p1 : List Nat := [40,105,110,118,32,40,43,32,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,58,108,99,109,36,57,32,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,58,108,99,109,36,49,49,41,41,0,0,0,0,0,0,1,0]
theorem C36_4p1bound : C36_4p1.all wordBound = true := (by decide : [40,105,110,118,32,40,43,32,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,58,108,99,109,36,57,32,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,58,108,99,109,36,49,49,41,41,0,0,0,0,0,0,1,0].all wordBound = true)

def C36_4words : List Nat := C36_4p0 ++ C36_4p1

theorem C36_4wire : C36_4.flatMap columnWords = C36_4words := by
  rfl

theorem C36_4wordBound : C36_4words.all wordBound = true := by
  simp only [C36_4words,List.all_append,C36_4p0bound,C36_4p1bound]
  try rfl

theorem C36_4bounded : ∀ n ∈ C36_4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using C36_4wordBound

theorem C36_4length : C36_4.length = 6 := by rfl

def M36 : Module := ⟨36, [109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108], false, false, C36_0 ++ C36_1 ++ C36_2 ++ C36_3 ++ C36_4, ((List.range 0).map (fun n => [n]))⟩

def M36prefix : List Nat := [36,16,109,97,116,95,109,117,108,95,105,110,116,101,114,110,97,108,0,0,0,0,38]
theorem M36prefixwordBound : M36prefix.all wordBound = true := by decide

def M36words : List Nat := M36prefix ++ C36_0words ++ C36_1words ++ C36_2words ++ C36_3words ++ C36_4words ++ [0]

theorem M36wire : module.encode M36 = M36words := by
  rw [module_fast]
  simp only [M36,moduleWords,List.length_append,List.flatMap_append,C36_0length,C36_1length,C36_2length,C36_3length,C36_4length,C36_0wire,C36_1wire,C36_2wire,C36_3wire,C36_4wire]
  rfl

theorem M36wordBound : M36words.all wordBound = true := by
  simp only [M36words,List.all_append,M36prefixwordBound,C36_0wordBound,C36_1wordBound,C36_2wordBound,C36_3wordBound,C36_4wordBound]
  decide

theorem M36bounded : ∀ n ∈ M36words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using M36wordBound

end DivRemFV.Replay
