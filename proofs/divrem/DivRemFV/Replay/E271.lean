import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def E271c0 : Entry := ⟨8672, 39, [108,111,111,107,117,112,95,115,101,108,95,49,50,50,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 94 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 122 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 94 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 122 (0)) .nil))) .nil))))⟩

def E271c0p0 : List Nat := [8672,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,50,35,48,0,39,0,0,50,2,1,4,1,1,94,0,1,1,121,0,1,3,0,1,1,1,122,0,0,0,1,4,1,2,1,3,0,1,1,1,94,0,0,1,3,0,1,1,1,121,0,0,0,1,1,122,0,0,0]
theorem E271c0p0bound : E271c0p0.all wordBound = true := (by decide : [8672,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,50,35,48,0,39,0,0,50,2,1,4,1,1,94,0,1,1,121,0,1,3,0,1,1,1,122,0,0,0,1,4,1,2,1,3,0,1,1,1,94,0,0,1,3,0,1,1,1,121,0,0,0,1,1,122,0,0,0].all wordBound = true)

def E271c0words : List Nat := E271c0p0

theorem E271c0wire : entryWords E271c0 = E271c0words := by
  rfl

theorem E271c0wordBound : E271c0words.all wordBound = true := by
  simp only [E271c0words,List.all_append,E271c0p0bound]
  try rfl

theorem E271c0bounded : ∀ n ∈ E271c0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c0wordBound

def E271c1 : Entry := ⟨8673, 39, [99,97,108,108,95,51,57,95,48,95,52,48], (.lookup [⟨39, (some (122)), #[65,66,67,3,4,5,6,7,8,9,10,11,12,13,14,15,45,46,47,50,51,52,53,59,24,25,26,27]⟩] [⟨40, (some (114)), #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]⟩])⟩

def E271c1p0 : List Nat := [8673,39,12,99,97,108,108,95,51,57,95,48,95,52,48,1,1,0,1,39,1,122,28,65,66,67,3,4,5,6,7,8,9,10,11,12,13,14,15,45,46,47,50,51,52,53,59,24,25,26,27,1,40,1,114,28,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]
theorem E271c1p0bound : E271c1p0.all wordBound = true := (by decide : [8673,39,12,99,97,108,108,95,51,57,95,48,95,52,48,1,1,0,1,39,1,122,28,65,66,67,3,4,5,6,7,8,9,10,11,12,13,14,15,45,46,47,50,51,52,53,59,24,25,26,27,1,40,1,114,28,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27].all wordBound = true)

def E271c1words : List Nat := E271c1p0

theorem E271c1wire : entryWords E271c1 = E271c1words := by
  rfl

theorem E271c1wordBound : E271c1words.all wordBound = true := by
  simp only [E271c1words,List.all_append,E271c1p0bound]
  try rfl

theorem E271c1bounded : ∀ n ∈ E271c1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c1wordBound

def E271c2 : Entry := ⟨8674, 39, [108,111,111,107,117,112,95,115,101,108,95,49,50,51,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 72 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 123 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 72 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 123 (0)) .nil))) .nil))))⟩

def E271c2p0 : List Nat := [8674,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,51,35,48,0,39,0,0,50,2,1,4,1,1,72,0,1,1,121,0,1,3,0,1,1,1,123,0,0,0,1,4,1,2,1,3,0,1,1,1,72,0,0,1,3,0,1,1,1,121,0,0,0,1,1,123,0,0,0]
theorem E271c2p0bound : E271c2p0.all wordBound = true := (by decide : [8674,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,51,35,48,0,39,0,0,50,2,1,4,1,1,72,0,1,1,121,0,1,3,0,1,1,1,123,0,0,0,1,4,1,2,1,3,0,1,1,1,72,0,0,1,3,0,1,1,1,121,0,0,0,1,1,123,0,0,0].all wordBound = true)

def E271c2words : List Nat := E271c2p0

theorem E271c2wire : entryWords E271c2 = E271c2words := by
  rfl

theorem E271c2wordBound : E271c2words.all wordBound = true := by
  simp only [E271c2words,List.all_append,E271c2p0bound]
  try rfl

theorem E271c2bounded : ∀ n ∈ E271c2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c2wordBound

def E271c3 : Entry := ⟨8675, 39, [99,97,108,108,95,51,57,95,48,95,52,55], (.lookup [⟨39, (some (123)), #[3,4,5,54,55,56,57,45,46,47,53]⟩] [⟨47, (some (41)), #[0,1,2,3,4,5,6,7,8,9,10]⟩])⟩

def E271c3p0 : List Nat := [8675,39,12,99,97,108,108,95,51,57,95,48,95,52,55,1,1,0,1,39,1,123,11,3,4,5,54,55,56,57,45,46,47,53,1,47,1,41,11,0,1,2,3,4,5,6,7,8,9,10]
theorem E271c3p0bound : E271c3p0.all wordBound = true := (by decide : [8675,39,12,99,97,108,108,95,51,57,95,48,95,52,55,1,1,0,1,39,1,123,11,3,4,5,54,55,56,57,45,46,47,53,1,47,1,41,11,0,1,2,3,4,5,6,7,8,9,10].all wordBound = true)

def E271c3words : List Nat := E271c3p0

theorem E271c3wire : entryWords E271c3 = E271c3words := by
  rfl

theorem E271c3wordBound : E271c3words.all wordBound = true := by
  simp only [E271c3words,List.all_append,E271c3p0bound]
  try rfl

theorem E271c3bounded : ∀ n ∈ E271c3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c3wordBound

def E271c4 : Entry := ⟨8676, 39, [108,111,111,107,117,112,95,115,101,108,95,49,50,52,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 73 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 124 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 73 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 124 (0)) .nil))) .nil))))⟩

def E271c4p0 : List Nat := [8676,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,52,35,48,0,39,0,0,50,2,1,4,1,1,73,0,1,1,121,0,1,3,0,1,1,1,124,0,0,0,1,4,1,2,1,3,0,1,1,1,73,0,0,1,3,0,1,1,1,121,0,0,0,1,1,124,0,0,0]
theorem E271c4p0bound : E271c4p0.all wordBound = true := (by decide : [8676,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,52,35,48,0,39,0,0,50,2,1,4,1,1,73,0,1,1,121,0,1,3,0,1,1,1,124,0,0,0,1,4,1,2,1,3,0,1,1,1,73,0,0,1,3,0,1,1,1,121,0,0,0,1,1,124,0,0,0].all wordBound = true)

def E271c4words : List Nat := E271c4p0

theorem E271c4wire : entryWords E271c4 = E271c4words := by
  rfl

theorem E271c4wordBound : E271c4words.all wordBound = true := by
  simp only [E271c4words,List.all_append,E271c4p0bound]
  try rfl

theorem E271c4bounded : ∀ n ∈ E271c4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c4wordBound

def E271c5 : Entry := ⟨8677, 39, [99,97,108,108,95,51,57,95,48,95,52,57], (.lookup [⟨39, (some (124)), #[3,4,5,54,55,56,57,47,59,68,45,46]⟩] [⟨49, (some (67)), #[0,1,2,3,4,5,6,7,8,9,10,11]⟩])⟩

def E271c5p0 : List Nat := [8677,39,12,99,97,108,108,95,51,57,95,48,95,52,57,1,1,0,1,39,1,124,12,3,4,5,54,55,56,57,47,59,68,45,46,1,49,1,67,12,0,1,2,3,4,5,6,7,8,9,10,11]
theorem E271c5p0bound : E271c5p0.all wordBound = true := (by decide : [8677,39,12,99,97,108,108,95,51,57,95,48,95,52,57,1,1,0,1,39,1,124,12,3,4,5,54,55,56,57,47,59,68,45,46,1,49,1,67,12,0,1,2,3,4,5,6,7,8,9,10,11].all wordBound = true)

def E271c5words : List Nat := E271c5p0

theorem E271c5wire : entryWords E271c5 = E271c5words := by
  rfl

theorem E271c5wordBound : E271c5words.all wordBound = true := by
  simp only [E271c5words,List.all_append,E271c5p0bound]
  try rfl

theorem E271c5bounded : ∀ n ∈ E271c5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c5wordBound

def E271c6 : Entry := ⟨8678, 39, [99,97,108,108,95,51,57,95,48,95,54,55], (.lookup [⟨39, (some (124)), #[45,46,50,51,52,53]⟩] [⟨67, (some (9)), #[0,1,2,3,4,5]⟩])⟩

def E271c6p0 : List Nat := [8678,39,12,99,97,108,108,95,51,57,95,48,95,54,55,1,1,0,1,39,1,124,6,45,46,50,51,52,53,1,67,1,9,6,0,1,2,3,4,5]
theorem E271c6p0bound : E271c6p0.all wordBound = true := (by decide : [8678,39,12,99,97,108,108,95,51,57,95,48,95,54,55,1,1,0,1,39,1,124,6,45,46,50,51,52,53,1,67,1,9,6,0,1,2,3,4,5].all wordBound = true)

def E271c6words : List Nat := E271c6p0

theorem E271c6wire : entryWords E271c6 = E271c6words := by
  rfl

theorem E271c6wordBound : E271c6words.all wordBound = true := by
  simp only [E271c6words,List.all_append,E271c6p0bound]
  try rfl

theorem E271c6bounded : ∀ n ∈ E271c6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c6wordBound

def E271c7 : Entry := ⟨8679, 39, [108,111,111,107,117,112,95,115,101,108,95,49,50,53,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 74 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 125 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 74 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 125 (0)) .nil))) .nil))))⟩

def E271c7p0 : List Nat := [8679,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,53,35,48,0,39,0,0,50,2,1,4,1,1,74,0,1,1,121,0,1,3,0,1,1,1,125,0,0,0,1,4,1,2,1,3,0,1,1,1,74,0,0,1,3,0,1,1,1,121,0,0,0,1,1,125,0,0,0]
theorem E271c7p0bound : E271c7p0.all wordBound = true := (by decide : [8679,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,53,35,48,0,39,0,0,50,2,1,4,1,1,74,0,1,1,121,0,1,3,0,1,1,1,125,0,0,0,1,4,1,2,1,3,0,1,1,1,74,0,0,1,3,0,1,1,1,121,0,0,0,1,1,125,0,0,0].all wordBound = true)

def E271c7words : List Nat := E271c7p0

theorem E271c7wire : entryWords E271c7 = E271c7words := by
  rfl

theorem E271c7wordBound : E271c7words.all wordBound = true := by
  simp only [E271c7words,List.all_append,E271c7p0bound]
  try rfl

theorem E271c7bounded : ∀ n ∈ E271c7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c7wordBound

def E271c8 : Entry := ⟨8680, 39, [99,97,108,108,95,51,57,95,48,95,53,48], (.lookup [⟨39, (some (125)), #[3,4,5,54,55,56,57,45,46,47,50,51,52,53]⟩] [⟨50, (some (45)), #[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩])⟩

def E271c8p0 : List Nat := [8680,39,12,99,97,108,108,95,51,57,95,48,95,53,48,1,1,0,1,39,1,125,14,3,4,5,54,55,56,57,45,46,47,50,51,52,53,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem E271c8p0bound : E271c8p0.all wordBound = true := (by decide : [8680,39,12,99,97,108,108,95,51,57,95,48,95,53,48,1,1,0,1,39,1,125,14,3,4,5,54,55,56,57,45,46,47,50,51,52,53,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13].all wordBound = true)

def E271c8words : List Nat := E271c8p0

theorem E271c8wire : entryWords E271c8 = E271c8words := by
  rfl

theorem E271c8wordBound : E271c8words.all wordBound = true := by
  simp only [E271c8words,List.all_append,E271c8p0bound]
  try rfl

theorem E271c8bounded : ∀ n ∈ E271c8words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c8wordBound

def E271c9 : Entry := ⟨8681, 39, [108,111,111,107,117,112,95,115,101,108,95,49,50,54,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 76 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 126 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 76 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 126 (0)) .nil))) .nil))))⟩

def E271c9p0 : List Nat := [8681,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,54,35,48,0,39,0,0,50,2,1,4,1,1,76,0,1,1,121,0,1,3,0,1,1,1,126,0,0,0,1,4,1,2,1,3,0,1,1,1,76,0,0,1,3,0,1,1,1,121,0,0,0,1,1,126,0,0,0]
theorem E271c9p0bound : E271c9p0.all wordBound = true := (by decide : [8681,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,54,35,48,0,39,0,0,50,2,1,4,1,1,76,0,1,1,121,0,1,3,0,1,1,1,126,0,0,0,1,4,1,2,1,3,0,1,1,1,76,0,0,1,3,0,1,1,1,121,0,0,0,1,1,126,0,0,0].all wordBound = true)

def E271c9words : List Nat := E271c9p0

theorem E271c9wire : entryWords E271c9 = E271c9words := by
  rfl

theorem E271c9wordBound : E271c9words.all wordBound = true := by
  simp only [E271c9words,List.all_append,E271c9p0bound]
  try rfl

theorem E271c9bounded : ∀ n ∈ E271c9words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c9wordBound

def E271c10 : Entry := ⟨8682, 39, [99,97,108,108,95,51,57,95,48,95,56,48], (.lookup [⟨39, (some (126)), #[36,37,38,39,48,50,51,52,53]⟩] [⟨80, (some (33)), #[0,1,2,3,4,5,6,7,8]⟩])⟩

def E271c10p0 : List Nat := [8682,39,12,99,97,108,108,95,51,57,95,48,95,56,48,1,1,0,1,39,1,126,9,36,37,38,39,48,50,51,52,53,1,80,1,33,9,0,1,2,3,4,5,6,7,8]
theorem E271c10p0bound : E271c10p0.all wordBound = true := (by decide : [8682,39,12,99,97,108,108,95,51,57,95,48,95,56,48,1,1,0,1,39,1,126,9,36,37,38,39,48,50,51,52,53,1,80,1,33,9,0,1,2,3,4,5,6,7,8].all wordBound = true)

def E271c10words : List Nat := E271c10p0

theorem E271c10wire : entryWords E271c10 = E271c10words := by
  rfl

theorem E271c10wordBound : E271c10words.all wordBound = true := by
  simp only [E271c10words,List.all_append,E271c10p0bound]
  try rfl

theorem E271c10bounded : ∀ n ∈ E271c10words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c10wordBound

def E271c11 : Entry := ⟨8683, 39, [108,111,111,107,117,112,95,115,101,108,95,49,50,55,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 77 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 127 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 77 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 127 (0)) .nil))) .nil))))⟩

def E271c11p0 : List Nat := [8683,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,55,35,48,0,39,0,0,50,2,1,4,1,1,77,0,1,1,121,0,1,3,0,1,1,1,127,0,0,0,1,4,1,2,1,3,0,1,1,1,77,0,0,1,3,0,1,1,1,121,0,0,0,1,1,127,0,0,0]
theorem E271c11p0bound : E271c11p0.all wordBound = true := (by decide : [8683,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,55,35,48,0,39,0,0,50,2,1,4,1,1,77,0,1,1,121,0,1,3,0,1,1,1,127,0,0,0,1,4,1,2,1,3,0,1,1,1,77,0,0,1,3,0,1,1,1,121,0,0,0,1,1,127,0,0,0].all wordBound = true)

def E271c11words : List Nat := E271c11p0

theorem E271c11wire : entryWords E271c11 = E271c11words := by
  rfl

theorem E271c11wordBound : E271c11words.all wordBound = true := by
  simp only [E271c11words,List.all_append,E271c11p0bound]
  try rfl

theorem E271c11bounded : ∀ n ∈ E271c11words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c11wordBound

def E271c12 : Entry := ⟨8684, 39, [99,97,108,108,95,51,57,95,48,95,56,48], (.lookup [⟨39, (some (127)), #[36,37,38,39,48,50,51,52,53]⟩] [⟨80, (some (33)), #[0,1,2,3,4,9,10,11,12]⟩])⟩

def E271c12p0 : List Nat := [8684,39,12,99,97,108,108,95,51,57,95,48,95,56,48,1,1,0,1,39,1,127,9,36,37,38,39,48,50,51,52,53,1,80,1,33,9,0,1,2,3,4,9,10,11,12]
theorem E271c12p0bound : E271c12p0.all wordBound = true := (by decide : [8684,39,12,99,97,108,108,95,51,57,95,48,95,56,48,1,1,0,1,39,1,127,9,36,37,38,39,48,50,51,52,53,1,80,1,33,9,0,1,2,3,4,9,10,11,12].all wordBound = true)

def E271c12words : List Nat := E271c12p0

theorem E271c12wire : entryWords E271c12 = E271c12words := by
  rfl

theorem E271c12wordBound : E271c12words.all wordBound = true := by
  simp only [E271c12words,List.all_append,E271c12p0bound]
  try rfl

theorem E271c12bounded : ∀ n ∈ E271c12words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c12wordBound

def E271c13 : Entry := ⟨8685, 39, [108,111,111,107,117,112,95,115,101,108,95,49,50,56,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 78 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 128 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 78 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 128 (0)) .nil))) .nil))))⟩

def E271c13p0 : List Nat := [8685,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,56,35,48,0,39,0,0,50,2,1,4,1,1,78,0,1,1,121,0,1,3,0,1,1,1,128,0,0,0,1,4,1,2,1,3,0,1,1,1,78,0,0,1,3,0,1,1,1,121,0,0,0,1,1,128,0,0,0]
theorem E271c13p0bound : E271c13p0.all wordBound = true := (by decide : [8685,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,56,35,48,0,39,0,0,50,2,1,4,1,1,78,0,1,1,121,0,1,3,0,1,1,1,128,0,0,0,1,4,1,2,1,3,0,1,1,1,78,0,0,1,3,0,1,1,1,121,0,0,0,1,1,128,0,0,0].all wordBound = true)

def E271c13words : List Nat := E271c13p0

theorem E271c13wire : entryWords E271c13 = E271c13words := by
  rfl

theorem E271c13wordBound : E271c13words.all wordBound = true := by
  simp only [E271c13words,List.all_append,E271c13p0bound]
  try rfl

theorem E271c13bounded : ∀ n ∈ E271c13words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c13wordBound

def E271c14 : Entry := ⟨8686, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (128)), #[39,32,53]⟩] [⟨83, (some (15)), #[0,1,2]⟩])⟩

def E271c14p0 : List Nat := [8686,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,128,3,39,32,53,1,83,1,15,3,0,1,2]
theorem E271c14p0bound : E271c14p0.all wordBound = true := (by decide : [8686,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,128,3,39,32,53,1,83,1,15,3,0,1,2].all wordBound = true)

def E271c14words : List Nat := E271c14p0

theorem E271c14wire : entryWords E271c14 = E271c14words := by
  rfl

theorem E271c14wordBound : E271c14words.all wordBound = true := by
  simp only [E271c14words,List.all_append,E271c14p0bound]
  try rfl

theorem E271c14bounded : ∀ n ∈ E271c14words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c14wordBound

def E271c15 : Entry := ⟨8687, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (128)), #[38,31,52]⟩] [⟨83, (some (15)), #[0,1,2]⟩])⟩

def E271c15p0 : List Nat := [8687,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,128,3,38,31,52,1,83,1,15,3,0,1,2]
theorem E271c15p0bound : E271c15p0.all wordBound = true := (by decide : [8687,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,128,3,38,31,52,1,83,1,15,3,0,1,2].all wordBound = true)

def E271c15words : List Nat := E271c15p0

theorem E271c15wire : entryWords E271c15 = E271c15words := by
  rfl

theorem E271c15wordBound : E271c15words.all wordBound = true := by
  simp only [E271c15words,List.all_append,E271c15p0bound]
  try rfl

theorem E271c15bounded : ∀ n ∈ E271c15words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c15wordBound

def E271c16 : Entry := ⟨8688, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (128)), #[37,30,51]⟩] [⟨83, (some (15)), #[0,1,2]⟩])⟩

def E271c16p0 : List Nat := [8688,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,128,3,37,30,51,1,83,1,15,3,0,1,2]
theorem E271c16p0bound : E271c16p0.all wordBound = true := (by decide : [8688,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,128,3,37,30,51,1,83,1,15,3,0,1,2].all wordBound = true)

def E271c16words : List Nat := E271c16p0

theorem E271c16wire : entryWords E271c16 = E271c16words := by
  rfl

theorem E271c16wordBound : E271c16words.all wordBound = true := by
  simp only [E271c16words,List.all_append,E271c16p0bound]
  try rfl

theorem E271c16bounded : ∀ n ∈ E271c16words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c16wordBound

def E271c17 : Entry := ⟨8689, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (128)), #[36,29,50]⟩] [⟨83, (some (15)), #[0,1,2]⟩])⟩

def E271c17p0 : List Nat := [8689,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,128,3,36,29,50,1,83,1,15,3,0,1,2]
theorem E271c17p0bound : E271c17p0.all wordBound = true := (by decide : [8689,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,128,3,36,29,50,1,83,1,15,3,0,1,2].all wordBound = true)

def E271c17words : List Nat := E271c17p0

theorem E271c17wire : entryWords E271c17 = E271c17words := by
  rfl

theorem E271c17wordBound : E271c17words.all wordBound = true := by
  simp only [E271c17words,List.all_append,E271c17p0bound]
  try rfl

theorem E271c17bounded : ∀ n ∈ E271c17words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c17wordBound

def E271c18 : Entry := ⟨8690, 39, [108,111,111,107,117,112,95,115,101,108,95,49,50,57,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 79 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 129 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 79 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 129 (0)) .nil))) .nil))))⟩

def E271c18p0 : List Nat := [8690,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,57,35,48,0,39,0,0,50,2,1,4,1,1,79,0,1,1,121,0,1,3,0,1,1,1,129,0,0,0,1,4,1,2,1,3,0,1,1,1,79,0,0,1,3,0,1,1,1,121,0,0,0,1,1,129,0,0,0]
theorem E271c18p0bound : E271c18p0.all wordBound = true := (by decide : [8690,39,16,108,111,111,107,117,112,95,115,101,108,95,49,50,57,35,48,0,39,0,0,50,2,1,4,1,1,79,0,1,1,121,0,1,3,0,1,1,1,129,0,0,0,1,4,1,2,1,3,0,1,1,1,79,0,0,1,3,0,1,1,1,121,0,0,0,1,1,129,0,0,0].all wordBound = true)

def E271c18words : List Nat := E271c18p0

theorem E271c18wire : entryWords E271c18 = E271c18words := by
  rfl

theorem E271c18wordBound : E271c18words.all wordBound = true := by
  simp only [E271c18words,List.all_append,E271c18p0bound]
  try rfl

theorem E271c18bounded : ∀ n ∈ E271c18words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c18wordBound

def E271c19 : Entry := ⟨8691, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (129)), #[39,32,53]⟩] [⟨83, (some (15)), #[0,1,4]⟩])⟩

def E271c19p0 : List Nat := [8691,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,129,3,39,32,53,1,83,1,15,3,0,1,4]
theorem E271c19p0bound : E271c19p0.all wordBound = true := (by decide : [8691,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,129,3,39,32,53,1,83,1,15,3,0,1,4].all wordBound = true)

def E271c19words : List Nat := E271c19p0

theorem E271c19wire : entryWords E271c19 = E271c19words := by
  rfl

theorem E271c19wordBound : E271c19words.all wordBound = true := by
  simp only [E271c19words,List.all_append,E271c19p0bound]
  try rfl

theorem E271c19bounded : ∀ n ∈ E271c19words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c19wordBound

def E271c20 : Entry := ⟨8692, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (129)), #[38,31,52]⟩] [⟨83, (some (15)), #[0,1,4]⟩])⟩

def E271c20p0 : List Nat := [8692,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,129,3,38,31,52,1,83,1,15,3,0,1,4]
theorem E271c20p0bound : E271c20p0.all wordBound = true := (by decide : [8692,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,129,3,38,31,52,1,83,1,15,3,0,1,4].all wordBound = true)

def E271c20words : List Nat := E271c20p0

theorem E271c20wire : entryWords E271c20 = E271c20words := by
  rfl

theorem E271c20wordBound : E271c20words.all wordBound = true := by
  simp only [E271c20words,List.all_append,E271c20p0bound]
  try rfl

theorem E271c20bounded : ∀ n ∈ E271c20words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c20wordBound

def E271c21 : Entry := ⟨8693, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (129)), #[37,30,51]⟩] [⟨83, (some (15)), #[0,1,4]⟩])⟩

def E271c21p0 : List Nat := [8693,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,129,3,37,30,51,1,83,1,15,3,0,1,4]
theorem E271c21p0bound : E271c21p0.all wordBound = true := (by decide : [8693,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,129,3,37,30,51,1,83,1,15,3,0,1,4].all wordBound = true)

def E271c21words : List Nat := E271c21p0

theorem E271c21wire : entryWords E271c21 = E271c21words := by
  rfl

theorem E271c21wordBound : E271c21words.all wordBound = true := by
  simp only [E271c21words,List.all_append,E271c21p0bound]
  try rfl

theorem E271c21bounded : ∀ n ∈ E271c21words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c21wordBound

def E271c22 : Entry := ⟨8694, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (129)), #[36,29,50]⟩] [⟨83, (some (15)), #[0,1,4]⟩])⟩

def E271c22p0 : List Nat := [8694,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,129,3,36,29,50,1,83,1,15,3,0,1,4]
theorem E271c22p0bound : E271c22p0.all wordBound = true := (by decide : [8694,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,129,3,36,29,50,1,83,1,15,3,0,1,4].all wordBound = true)

def E271c22words : List Nat := E271c22p0

theorem E271c22wire : entryWords E271c22 = E271c22words := by
  rfl

theorem E271c22wordBound : E271c22words.all wordBound = true := by
  simp only [E271c22words,List.all_append,E271c22p0bound]
  try rfl

theorem E271c22bounded : ∀ n ∈ E271c22words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c22wordBound

def E271c23 : Entry := ⟨8695, 39, [108,111,111,107,117,112,95,115,101,108,95,49,51,48,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 81 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 130 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 81 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 130 (0)) .nil))) .nil))))⟩

def E271c23p0 : List Nat := [8695,39,16,108,111,111,107,117,112,95,115,101,108,95,49,51,48,35,48,0,39,0,0,50,2,1,4,1,1,81,0,1,1,121,0,1,3,0,1,1,1,130,0,0,0,1,4,1,2,1,3,0,1,1,1,81,0,0,1,3,0,1,1,1,121,0,0,0,1,1,130,0,0,0]
theorem E271c23p0bound : E271c23p0.all wordBound = true := (by decide : [8695,39,16,108,111,111,107,117,112,95,115,101,108,95,49,51,48,35,48,0,39,0,0,50,2,1,4,1,1,81,0,1,1,121,0,1,3,0,1,1,1,130,0,0,0,1,4,1,2,1,3,0,1,1,1,81,0,0,1,3,0,1,1,1,121,0,0,0,1,1,130,0,0,0].all wordBound = true)

def E271c23words : List Nat := E271c23p0

theorem E271c23wire : entryWords E271c23 = E271c23words := by
  rfl

theorem E271c23wordBound : E271c23words.all wordBound = true := by
  simp only [E271c23words,List.all_append,E271c23p0bound]
  try rfl

theorem E271c23bounded : ∀ n ∈ E271c23words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c23wordBound

def E271c24 : Entry := ⟨8696, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (130)), #[39,43,53]⟩] [⟨83, (some (15)), #[0,1,2]⟩])⟩

def E271c24p0 : List Nat := [8696,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,130,3,39,43,53,1,83,1,15,3,0,1,2]
theorem E271c24p0bound : E271c24p0.all wordBound = true := (by decide : [8696,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,130,3,39,43,53,1,83,1,15,3,0,1,2].all wordBound = true)

def E271c24words : List Nat := E271c24p0

theorem E271c24wire : entryWords E271c24 = E271c24words := by
  rfl

theorem E271c24wordBound : E271c24words.all wordBound = true := by
  simp only [E271c24words,List.all_append,E271c24p0bound]
  try rfl

theorem E271c24bounded : ∀ n ∈ E271c24words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c24wordBound

def E271c25 : Entry := ⟨8697, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (130)), #[38,42,52]⟩] [⟨83, (some (15)), #[0,1,2]⟩])⟩

def E271c25p0 : List Nat := [8697,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,130,3,38,42,52,1,83,1,15,3,0,1,2]
theorem E271c25p0bound : E271c25p0.all wordBound = true := (by decide : [8697,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,130,3,38,42,52,1,83,1,15,3,0,1,2].all wordBound = true)

def E271c25words : List Nat := E271c25p0

theorem E271c25wire : entryWords E271c25 = E271c25words := by
  rfl

theorem E271c25wordBound : E271c25words.all wordBound = true := by
  simp only [E271c25words,List.all_append,E271c25p0bound]
  try rfl

theorem E271c25bounded : ∀ n ∈ E271c25words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c25wordBound

def E271c26 : Entry := ⟨8698, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (130)), #[37,41,51]⟩] [⟨83, (some (15)), #[0,1,2]⟩])⟩

def E271c26p0 : List Nat := [8698,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,130,3,37,41,51,1,83,1,15,3,0,1,2]
theorem E271c26p0bound : E271c26p0.all wordBound = true := (by decide : [8698,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,130,3,37,41,51,1,83,1,15,3,0,1,2].all wordBound = true)

def E271c26words : List Nat := E271c26p0

theorem E271c26wire : entryWords E271c26 = E271c26words := by
  rfl

theorem E271c26wordBound : E271c26words.all wordBound = true := by
  simp only [E271c26words,List.all_append,E271c26p0bound]
  try rfl

theorem E271c26bounded : ∀ n ∈ E271c26words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c26wordBound

def E271c27 : Entry := ⟨8699, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (130)), #[36,40,50]⟩] [⟨83, (some (15)), #[0,1,2]⟩])⟩

def E271c27p0 : List Nat := [8699,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,130,3,36,40,50,1,83,1,15,3,0,1,2]
theorem E271c27p0bound : E271c27p0.all wordBound = true := (by decide : [8699,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,130,3,36,40,50,1,83,1,15,3,0,1,2].all wordBound = true)

def E271c27words : List Nat := E271c27p0

theorem E271c27wire : entryWords E271c27 = E271c27words := by
  rfl

theorem E271c27wordBound : E271c27words.all wordBound = true := by
  simp only [E271c27words,List.all_append,E271c27p0bound]
  try rfl

theorem E271c27bounded : ∀ n ∈ E271c27words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c27wordBound

def E271c28 : Entry := ⟨8700, 39, [108,111,111,107,117,112,95,115,101,108,95,49,51,49,35,48], (.vanishing 39 none (.sum (.cons (.product (.cons (.column 82 (0)) (.cons (.column 121 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 131 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 82 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 121 (0)) .nil)) .nil))) (.cons (.column 131 (0)) .nil))) .nil))))⟩

def E271c28p0 : List Nat := [8700,39,16,108,111,111,107,117,112,95,115,101,108,95,49,51,49,35,48,0,39,0,0,50,2,1,4,1,1,82,0,1,1,121,0,1,3,0,1,1,1,131,0,0,0,1,4,1,2,1,3,0,1,1,1,82,0,0,1,3,0,1,1,1,121,0,0,0,1,1,131,0,0,0]
theorem E271c28p0bound : E271c28p0.all wordBound = true := (by decide : [8700,39,16,108,111,111,107,117,112,95,115,101,108,95,49,51,49,35,48,0,39,0,0,50,2,1,4,1,1,82,0,1,1,121,0,1,3,0,1,1,1,131,0,0,0,1,4,1,2,1,3,0,1,1,1,82,0,0,1,3,0,1,1,1,121,0,0,0,1,1,131,0,0,0].all wordBound = true)

def E271c28words : List Nat := E271c28p0

theorem E271c28wire : entryWords E271c28 = E271c28words := by
  rfl

theorem E271c28wordBound : E271c28words.all wordBound = true := by
  simp only [E271c28words,List.all_append,E271c28p0bound]
  try rfl

theorem E271c28bounded : ∀ n ∈ E271c28words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c28wordBound

def E271c29 : Entry := ⟨8701, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (131)), #[39,43,53]⟩] [⟨83, (some (15)), #[0,1,3]⟩])⟩

def E271c29p0 : List Nat := [8701,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,131,3,39,43,53,1,83,1,15,3,0,1,3]
theorem E271c29p0bound : E271c29p0.all wordBound = true := (by decide : [8701,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,131,3,39,43,53,1,83,1,15,3,0,1,3].all wordBound = true)

def E271c29words : List Nat := E271c29p0

theorem E271c29wire : entryWords E271c29 = E271c29words := by
  rfl

theorem E271c29wordBound : E271c29words.all wordBound = true := by
  simp only [E271c29words,List.all_append,E271c29p0bound]
  try rfl

theorem E271c29bounded : ∀ n ∈ E271c29words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c29wordBound

def E271c30 : Entry := ⟨8702, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (131)), #[38,42,52]⟩] [⟨83, (some (15)), #[0,1,3]⟩])⟩

def E271c30p0 : List Nat := [8702,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,131,3,38,42,52,1,83,1,15,3,0,1,3]
theorem E271c30p0bound : E271c30p0.all wordBound = true := (by decide : [8702,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,131,3,38,42,52,1,83,1,15,3,0,1,3].all wordBound = true)

def E271c30words : List Nat := E271c30p0

theorem E271c30wire : entryWords E271c30 = E271c30words := by
  rfl

theorem E271c30wordBound : E271c30words.all wordBound = true := by
  simp only [E271c30words,List.all_append,E271c30p0bound]
  try rfl

theorem E271c30bounded : ∀ n ∈ E271c30words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c30wordBound

def E271c31 : Entry := ⟨8703, 39, [99,97,108,108,95,51,57,95,48,95,56,51], (.lookup [⟨39, (some (131)), #[37,41,51]⟩] [⟨83, (some (15)), #[0,1,3]⟩])⟩

def E271c31p0 : List Nat := [8703,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,131,3,37,41,51,1,83,1,15,3,0,1,3]
theorem E271c31p0bound : E271c31p0.all wordBound = true := (by decide : [8703,39,12,99,97,108,108,95,51,57,95,48,95,56,51,1,1,0,1,39,1,131,3,37,41,51,1,83,1,15,3,0,1,3].all wordBound = true)

def E271c31words : List Nat := E271c31p0

theorem E271c31wire : entryWords E271c31 = E271c31words := by
  rfl

theorem E271c31wordBound : E271c31words.all wordBound = true := by
  simp only [E271c31words,List.all_append,E271c31p0bound]
  try rfl

theorem E271c31bounded : ∀ n ∈ E271c31words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E271c31wordBound

def E271 : List Entry := [E271c0,E271c1,E271c2,E271c3,E271c4,E271c5,E271c6,E271c7,E271c8,E271c9,E271c10,E271c11,E271c12,E271c13,E271c14,E271c15,E271c16,E271c17,E271c18,E271c19,E271c20,E271c21,E271c22,E271c23,E271c24,E271c25,E271c26,E271c27,E271c28,E271c29,E271c30,E271c31]

def E271words : List Nat := E271c0words ++ E271c1words ++ E271c2words ++ E271c3words ++ E271c4words ++ E271c5words ++ E271c6words ++ E271c7words ++ E271c8words ++ E271c9words ++ E271c10words ++ E271c11words ++ E271c12words ++ E271c13words ++ E271c14words ++ E271c15words ++ E271c16words ++ E271c17words ++ E271c18words ++ E271c19words ++ E271c20words ++ E271c21words ++ E271c22words ++ E271c23words ++ E271c24words ++ E271c25words ++ E271c26words ++ E271c27words ++ E271c28words ++ E271c29words ++ E271c30words ++ E271c31words

theorem E271wire : E271.flatMap entry.encode = E271words := by
  rw [entry_fast_fun]
  simp only [E271,List.flatMap_cons,List.flatMap_nil,List.append_nil,E271c0wire,E271c1wire,E271c2wire,E271c3wire,E271c4wire,E271c5wire,E271c6wire,E271c7wire,E271c8wire,E271c9wire,E271c10wire,E271c11wire,E271c12wire,E271c13wire,E271c14wire,E271c15wire,E271c16wire,E271c17wire,E271c18wire,E271c19wire,E271c20wire,E271c21wire,E271c22wire,E271c23wire,E271c24wire,E271c25wire,E271c26wire,E271c27wire,E271c28wire,E271c29wire,E271c30wire,E271c31wire]
  rfl

theorem E271wordBound : E271words.all wordBound = true := by
  simp only [E271words,List.all_append,E271c0wordBound,E271c1wordBound,E271c2wordBound,E271c3wordBound,E271c4wordBound,E271c5wordBound,E271c6wordBound,E271c7wordBound,E271c8wordBound,E271c9wordBound,E271c10wordBound,E271c11wordBound,E271c12wordBound,E271c13wordBound,E271c14wordBound,E271c15wordBound,E271c16wordBound,E271c17wordBound,E271c18wordBound,E271c19wordBound,E271c20wordBound,E271c21wordBound,E271c22wordBound,E271c23wordBound,E271c24wordBound,E271c25wordBound,E271c26wordBound,E271c27wordBound,E271c28wordBound,E271c29wordBound,E271c30wordBound,E271c31wordBound]
  decide

theorem E271bounded : ∀ n ∈ E271words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using E271wordBound

theorem E271length : E271.length = 32 := by rfl

def E271selected : List RawConstraint := []
theorem E271select : (E271.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).map Entry.rule = E271selected := by rfl

def E271incoming : List RawConstraint := []
theorem E271calls : (ArtifactBinding.incomingEntries ⟨[],E271⟩).map Entry.rule = E271incoming := by rfl

theorem E271closure : (E271.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).all (fun e => (ArtifactBinding.referencedModules e).all (fun id => decide (id ∈ ArtifactBinding.selectedIds))) = true := by decide

end DivRemFV.Replay
