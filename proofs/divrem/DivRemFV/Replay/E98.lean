import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def E98c0 : Entry := ⟨3136, 17, [112,99,50,35,51,52], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 34 (0)) (.cons (.column 2 (-1)) (.cons (.column 397 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c0p0 : List Nat := [3136,17,6,112,99,50,35,51,52,0,17,0,0,33,4,1,1,440,0,1,1,297,0,1,3,1,34,0,1,1,2,1,1,1,397,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c0p0bound : E98c0p0.all wordBound = true := (by decide : [3136,17,6,112,99,50,35,51,52,0,17,0,0,33,4,1,1,440,0,1,1,297,0,1,3,1,34,0,1,1,2,1,1,1,397,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c0words : List Nat := E98c0p0

theorem E98c0wire : entryWords E98c0 = E98c0words := by
  rfl

theorem E98c0wordBound : E98c0words.all wordBound = true := by
  simp only [E98c0words,List.all_append,E98c0p0bound]
  try rfl

theorem E98c0bounded : ∀ n ∈ E98c0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c0wordBound

def E98c1 : Entry := ⟨3137, 17, [112,99,50,35,51,53], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.column 297 (0)) (.cons (.difference (.sum (.cons (.column 38 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 398 (0)) .nil))) .nil))) (.cons (.column 3 (-1)) (.cons (.constant ⟨13, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c1p0 : List Nat := [3137,17,6,112,99,50,35,51,53,0,17,0,0,45,4,1,1,440,0,1,1,297,0,1,3,2,1,1,38,0,1,4,1,0,65536,1,1,398,0,0,0,1,1,3,1,1,0,13,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c1p0bound : E98c1p0.all wordBound = true := (by decide : [3137,17,6,112,99,50,35,51,53,0,17,0,0,45,4,1,1,440,0,1,1,297,0,1,3,2,1,1,38,0,1,4,1,0,65536,1,1,398,0,0,0,1,1,3,1,1,0,13,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c1words : List Nat := E98c1p0

theorem E98c1wire : entryWords E98c1 = E98c1words := by
  rfl

theorem E98c1wordBound : E98c1words.all wordBound = true := by
  simp only [E98c1words,List.all_append,E98c1p0bound]
  try rfl

theorem E98c1bounded : ∀ n ∈ E98c1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c1wordBound

def E98c2 : Entry := ⟨3138, 17, [112,99,50,35,51,54], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 37 (0)) (.cons (.column 2 (-1)) (.cons (.column 398 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c2p0 : List Nat := [3138,17,6,112,99,50,35,51,54,0,17,0,0,33,4,1,1,440,0,1,1,297,0,1,3,1,37,0,1,1,2,1,1,1,398,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c2p0bound : E98c2p0.all wordBound = true := (by decide : [3138,17,6,112,99,50,35,51,54,0,17,0,0,33,4,1,1,440,0,1,1,297,0,1,3,1,37,0,1,1,2,1,1,1,398,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c2words : List Nat := E98c2p0

theorem E98c2wire : entryWords E98c2 = E98c2words := by
  rfl

theorem E98c2wordBound : E98c2words.all wordBound = true := by
  simp only [E98c2words,List.all_append,E98c2p0bound]
  try rfl

theorem E98c2bounded : ∀ n ∈ E98c2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c2wordBound

def E98c3 : Entry := ⟨3139, 17, [112,99,50,35,51,55], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.column 297 (0)) (.cons (.difference (.sum (.cons (.column 40 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 399 (0)) .nil))) .nil))) (.cons (.column 3 (-1)) (.cons (.constant ⟨14, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c3p0 : List Nat := [3139,17,6,112,99,50,35,51,55,0,17,0,0,45,4,1,1,440,0,1,1,297,0,1,3,2,1,1,40,0,1,4,1,0,65536,1,1,399,0,0,0,1,1,3,1,1,0,14,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c3p0bound : E98c3p0.all wordBound = true := (by decide : [3139,17,6,112,99,50,35,51,55,0,17,0,0,45,4,1,1,440,0,1,1,297,0,1,3,2,1,1,40,0,1,4,1,0,65536,1,1,399,0,0,0,1,1,3,1,1,0,14,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c3words : List Nat := E98c3p0

theorem E98c3wire : entryWords E98c3 = E98c3words := by
  rfl

theorem E98c3wordBound : E98c3words.all wordBound = true := by
  simp only [E98c3words,List.all_append,E98c3p0bound]
  try rfl

theorem E98c3bounded : ∀ n ∈ E98c3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c3wordBound

def E98c4 : Entry := ⟨3140, 17, [112,99,50,35,51,56], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 39 (0)) (.cons (.column 2 (-1)) (.cons (.column 399 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c4p0 : List Nat := [3140,17,6,112,99,50,35,51,56,0,17,0,0,33,4,1,1,440,0,1,1,297,0,1,3,1,39,0,1,1,2,1,1,1,399,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c4p0bound : E98c4p0.all wordBound = true := (by decide : [3140,17,6,112,99,50,35,51,56,0,17,0,0,33,4,1,1,440,0,1,1,297,0,1,3,1,39,0,1,1,2,1,1,1,399,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c4words : List Nat := E98c4p0

theorem E98c4wire : entryWords E98c4 = E98c4words := by
  rfl

theorem E98c4wordBound : E98c4words.all wordBound = true := by
  simp only [E98c4words,List.all_append,E98c4p0bound]
  try rfl

theorem E98c4bounded : ∀ n ∈ E98c4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c4wordBound

def E98c5 : Entry := ⟨3141, 17, [112,99,50,35,51,57], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.column 297 (0)) (.cons (.difference (.sum (.cons (.column 3 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 400 (0)) .nil))) .nil))) (.cons (.column 3 (-1)) (.cons (.constant ⟨15, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c5p0 : List Nat := [3141,17,6,112,99,50,35,51,57,0,17,0,0,45,4,1,1,440,0,1,1,297,0,1,3,2,1,1,3,0,1,4,1,0,65536,1,1,400,0,0,0,1,1,3,1,1,0,15,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c5p0bound : E98c5p0.all wordBound = true := (by decide : [3141,17,6,112,99,50,35,51,57,0,17,0,0,45,4,1,1,440,0,1,1,297,0,1,3,2,1,1,3,0,1,4,1,0,65536,1,1,400,0,0,0,1,1,3,1,1,0,15,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c5words : List Nat := E98c5p0

theorem E98c5wire : entryWords E98c5 = E98c5words := by
  rfl

theorem E98c5wordBound : E98c5words.all wordBound = true := by
  simp only [E98c5words,List.all_append,E98c5p0bound]
  try rfl

theorem E98c5bounded : ∀ n ∈ E98c5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c5wordBound

def E98c6 : Entry := ⟨3142, 17, [112,99,50,35,52,48], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 2 (0)) (.cons (.column 2 (-1)) (.cons (.column 400 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c6p0 : List Nat := [3142,17,6,112,99,50,35,52,48,0,17,0,0,33,4,1,1,440,0,1,1,297,0,1,3,1,2,0,1,1,2,1,1,1,400,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c6p0bound : E98c6p0.all wordBound = true := (by decide : [3142,17,6,112,99,50,35,52,48,0,17,0,0,33,4,1,1,440,0,1,1,297,0,1,3,1,2,0,1,1,2,1,1,1,400,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c6words : List Nat := E98c6p0

theorem E98c6wire : entryWords E98c6 = E98c6words := by
  rfl

theorem E98c6wordBound : E98c6words.all wordBound = true := by
  simp only [E98c6words,List.all_append,E98c6p0bound]
  try rfl

theorem E98c6bounded : ∀ n ∈ E98c6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c6wordBound

def E98c7 : Entry := ⟨3143, 17, [112,99,50,35,52,49], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 2 (0)) (.cons (.column 2 (-1)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c7p0 : List Nat := [3143,17,6,112,99,50,35,52,49,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,2,0,1,1,2,1,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c7p0bound : E98c7p0.all wordBound = true := (by decide : [3143,17,6,112,99,50,35,52,49,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,2,0,1,1,2,1,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c7words : List Nat := E98c7p0

theorem E98c7wire : entryWords E98c7 = E98c7words := by
  rfl

theorem E98c7wordBound : E98c7words.all wordBound = true := by
  simp only [E98c7words,List.all_append,E98c7p0bound]
  try rfl

theorem E98c7bounded : ∀ n ∈ E98c7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c7wordBound

def E98c8 : Entry := ⟨3144, 17, [112,99,50,35,52,50], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 3 (0)) (.cons (.column 3 (-1)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c8p0 : List Nat := [3144,17,6,112,99,50,35,52,50,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,3,0,1,1,3,1,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c8p0bound : E98c8p0.all wordBound = true := (by decide : [3144,17,6,112,99,50,35,52,50,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,3,0,1,1,3,1,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c8words : List Nat := E98c8p0

theorem E98c8wire : entryWords E98c8 = E98c8words := by
  rfl

theorem E98c8wordBound : E98c8words.all wordBound = true := by
  simp only [E98c8words,List.all_append,E98c8p0bound]
  try rfl

theorem E98c8bounded : ∀ n ∈ E98c8words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c8wordBound

def E98c9 : Entry := ⟨3145, 17, [112,99,50,35,52,51], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.difference (.column 5 (0)) (.cons (.column 5 (-1)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil)))))⟩

def E98c9p0 : List Nat := [3145,17,6,112,99,50,35,52,51,0,17,0,0,25,4,1,1,440,0,1,3,1,5,0,1,1,5,1,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c9p0bound : E98c9p0.all wordBound = true := (by decide : [3145,17,6,112,99,50,35,52,51,0,17,0,0,25,4,1,1,440,0,1,3,1,5,0,1,1,5,1,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c9words : List Nat := E98c9p0

theorem E98c9wire : entryWords E98c9 = E98c9words := by
  rfl

theorem E98c9wordBound : E98c9words.all wordBound = true := by
  simp only [E98c9words,List.all_append,E98c9p0bound]
  try rfl

theorem E98c9bounded : ∀ n ∈ E98c9words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c9wordBound

def E98c10 : Entry := ⟨3146, 17, [112,99,50,35,52,52], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.difference (.column 7 (0)) (.cons (.column 7 (-1)) .nil)) .nil))))⟩

def E98c10p0 : List Nat := [3146,17,6,112,99,50,35,52,52,0,17,0,0,16,4,1,1,440,0,1,3,1,7,0,1,1,7,1,0,0]
theorem E98c10p0bound : E98c10p0.all wordBound = true := (by decide : [3146,17,6,112,99,50,35,52,52,0,17,0,0,16,4,1,1,440,0,1,3,1,7,0,1,1,7,1,0,0].all wordBound = true)

def E98c10words : List Nat := E98c10p0

theorem E98c10wire : entryWords E98c10 = E98c10words := by
  rfl

theorem E98c10wordBound : E98c10words.all wordBound = true := by
  simp only [E98c10words,List.all_append,E98c10p0bound]
  try rfl

theorem E98c10bounded : ∀ n ∈ E98c10words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c10wordBound

def E98c11 : Entry := ⟨3147, 17, [112,99,50,35,52,53], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 8 (0)) (.cons (.column 8 (-1)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c11p0 : List Nat := [3147,17,6,112,99,50,35,52,53,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,8,0,1,1,8,1,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c11p0bound : E98c11p0.all wordBound = true := (by decide : [3147,17,6,112,99,50,35,52,53,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,8,0,1,1,8,1,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c11words : List Nat := E98c11p0

theorem E98c11wire : entryWords E98c11 = E98c11words := by
  rfl

theorem E98c11wordBound : E98c11words.all wordBound = true := by
  simp only [E98c11words,List.all_append,E98c11p0bound]
  try rfl

theorem E98c11bounded : ∀ n ∈ E98c11words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c11wordBound

def E98c12 : Entry := ⟨3148, 17, [112,99,50,35,52,54], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 9 (0)) (.cons (.column 9 (-1)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c12p0 : List Nat := [3148,17,6,112,99,50,35,52,54,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,9,0,1,1,9,1,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c12p0bound : E98c12p0.all wordBound = true := (by decide : [3148,17,6,112,99,50,35,52,54,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,9,0,1,1,9,1,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c12words : List Nat := E98c12p0

theorem E98c12wire : entryWords E98c12 = E98c12words := by
  rfl

theorem E98c12wordBound : E98c12words.all wordBound = true := by
  simp only [E98c12words,List.all_append,E98c12p0bound]
  try rfl

theorem E98c12bounded : ∀ n ∈ E98c12words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c12wordBound

def E98c13 : Entry := ⟨3149, 17, [112,99,50,35,52,55], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 10 (0)) (.cons (.column 10 (-1)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c13p0 : List Nat := [3149,17,6,112,99,50,35,52,55,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,10,0,1,1,10,1,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c13p0bound : E98c13p0.all wordBound = true := (by decide : [3149,17,6,112,99,50,35,52,55,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,10,0,1,1,10,1,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c13words : List Nat := E98c13p0

theorem E98c13wire : entryWords E98c13 = E98c13words := by
  rfl

theorem E98c13wordBound : E98c13words.all wordBound = true := by
  simp only [E98c13words,List.all_append,E98c13p0bound]
  try rfl

theorem E98c13bounded : ∀ n ∈ E98c13words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c13wordBound

def E98c14 : Entry := ⟨3150, 17, [112,99,50,35,52,56], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 11 (0)) (.cons (.column 11 (-1)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E98c14p0 : List Nat := [3150,17,6,112,99,50,35,52,56,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,11,0,1,1,11,1,0,1,3,0,1,1,1,295,0,0,0]
theorem E98c14p0bound : E98c14p0.all wordBound = true := (by decide : [3150,17,6,112,99,50,35,52,56,0,17,0,0,41,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,11,0,1,1,11,1,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E98c14words : List Nat := E98c14p0

theorem E98c14wire : entryWords E98c14 = E98c14words := by
  rfl

theorem E98c14wordBound : E98c14words.all wordBound = true := by
  simp only [E98c14words,List.all_append,E98c14p0bound]
  try rfl

theorem E98c14bounded : ∀ n ∈ E98c14words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c14wordBound

def E98c15 : Entry := ⟨3151, 17, [112,99,50,35,52,57], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 12 (0)) (.cons (.column 12 (-1)) .nil)) .nil)))))⟩

def E98c15p0 : List Nat := [3151,17,6,112,99,50,35,52,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,12,0,1,1,12,1,0,0]
theorem E98c15p0bound : E98c15p0.all wordBound = true := (by decide : [3151,17,6,112,99,50,35,52,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,12,0,1,1,12,1,0,0].all wordBound = true)

def E98c15words : List Nat := E98c15p0

theorem E98c15wire : entryWords E98c15 = E98c15words := by
  rfl

theorem E98c15wordBound : E98c15words.all wordBound = true := by
  simp only [E98c15words,List.all_append,E98c15p0bound]
  try rfl

theorem E98c15bounded : ∀ n ∈ E98c15words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c15wordBound

def E98c16 : Entry := ⟨3152, 17, [112,99,50,35,53,48], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 13 (0)) (.cons (.column 13 (-1)) .nil)) .nil)))))⟩

def E98c16p0 : List Nat := [3152,17,6,112,99,50,35,53,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,13,0,1,1,13,1,0,0]
theorem E98c16p0bound : E98c16p0.all wordBound = true := (by decide : [3152,17,6,112,99,50,35,53,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,13,0,1,1,13,1,0,0].all wordBound = true)

def E98c16words : List Nat := E98c16p0

theorem E98c16wire : entryWords E98c16 = E98c16words := by
  rfl

theorem E98c16wordBound : E98c16words.all wordBound = true := by
  simp only [E98c16words,List.all_append,E98c16p0bound]
  try rfl

theorem E98c16bounded : ∀ n ∈ E98c16words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c16wordBound

def E98c17 : Entry := ⟨3153, 17, [112,99,50,35,53,49], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 14 (0)) (.cons (.column 14 (-1)) .nil)) .nil)))))⟩

def E98c17p0 : List Nat := [3153,17,6,112,99,50,35,53,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,14,0,1,1,14,1,0,0]
theorem E98c17p0bound : E98c17p0.all wordBound = true := (by decide : [3153,17,6,112,99,50,35,53,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,14,0,1,1,14,1,0,0].all wordBound = true)

def E98c17words : List Nat := E98c17p0

theorem E98c17wire : entryWords E98c17 = E98c17words := by
  rfl

theorem E98c17wordBound : E98c17words.all wordBound = true := by
  simp only [E98c17words,List.all_append,E98c17p0bound]
  try rfl

theorem E98c17bounded : ∀ n ∈ E98c17words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c17wordBound

def E98c18 : Entry := ⟨3154, 17, [112,99,50,35,53,50], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 15 (0)) (.cons (.column 15 (-1)) .nil)) .nil)))))⟩

def E98c18p0 : List Nat := [3154,17,6,112,99,50,35,53,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,15,0,1,1,15,1,0,0]
theorem E98c18p0bound : E98c18p0.all wordBound = true := (by decide : [3154,17,6,112,99,50,35,53,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,15,0,1,1,15,1,0,0].all wordBound = true)

def E98c18words : List Nat := E98c18p0

theorem E98c18wire : entryWords E98c18 = E98c18words := by
  rfl

theorem E98c18wordBound : E98c18words.all wordBound = true := by
  simp only [E98c18words,List.all_append,E98c18p0bound]
  try rfl

theorem E98c18bounded : ∀ n ∈ E98c18words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c18wordBound

def E98c19 : Entry := ⟨3155, 17, [112,99,50,35,53,51], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.difference (.column 16 (0)) (.cons (.column 16 (-1)) .nil)) .nil))))⟩

def E98c19p0 : List Nat := [3155,17,6,112,99,50,35,53,51,0,17,0,0,16,4,1,1,440,0,1,3,1,16,0,1,1,16,1,0,0]
theorem E98c19p0bound : E98c19p0.all wordBound = true := (by decide : [3155,17,6,112,99,50,35,53,51,0,17,0,0,16,4,1,1,440,0,1,3,1,16,0,1,1,16,1,0,0].all wordBound = true)

def E98c19words : List Nat := E98c19p0

theorem E98c19wire : entryWords E98c19 = E98c19words := by
  rfl

theorem E98c19wordBound : E98c19words.all wordBound = true := by
  simp only [E98c19words,List.all_append,E98c19p0bound]
  try rfl

theorem E98c19bounded : ∀ n ∈ E98c19words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c19wordBound

def E98c20 : Entry := ⟨3156, 17, [112,99,50,35,53,52], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 17 (0)) (.cons (.column 17 (-1)) .nil)) .nil)))))⟩

def E98c20p0 : List Nat := [3156,17,6,112,99,50,35,53,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,17,0,1,1,17,1,0,0]
theorem E98c20p0bound : E98c20p0.all wordBound = true := (by decide : [3156,17,6,112,99,50,35,53,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,17,0,1,1,17,1,0,0].all wordBound = true)

def E98c20words : List Nat := E98c20p0

theorem E98c20wire : entryWords E98c20 = E98c20words := by
  rfl

theorem E98c20wordBound : E98c20words.all wordBound = true := by
  simp only [E98c20words,List.all_append,E98c20p0bound]
  try rfl

theorem E98c20bounded : ∀ n ∈ E98c20words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c20wordBound

def E98c21 : Entry := ⟨3157, 17, [112,99,50,35,53,53], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 18 (0)) (.cons (.column 18 (-1)) .nil)) .nil)))))⟩

def E98c21p0 : List Nat := [3157,17,6,112,99,50,35,53,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,18,0,1,1,18,1,0,0]
theorem E98c21p0bound : E98c21p0.all wordBound = true := (by decide : [3157,17,6,112,99,50,35,53,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,18,0,1,1,18,1,0,0].all wordBound = true)

def E98c21words : List Nat := E98c21p0

theorem E98c21wire : entryWords E98c21 = E98c21words := by
  rfl

theorem E98c21wordBound : E98c21words.all wordBound = true := by
  simp only [E98c21words,List.all_append,E98c21p0bound]
  try rfl

theorem E98c21bounded : ∀ n ∈ E98c21words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c21wordBound

def E98c22 : Entry := ⟨3158, 17, [112,99,50,35,53,54], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 19 (0)) (.cons (.column 19 (-1)) .nil)) .nil)))))⟩

def E98c22p0 : List Nat := [3158,17,6,112,99,50,35,53,54,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,19,0,1,1,19,1,0,0]
theorem E98c22p0bound : E98c22p0.all wordBound = true := (by decide : [3158,17,6,112,99,50,35,53,54,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,19,0,1,1,19,1,0,0].all wordBound = true)

def E98c22words : List Nat := E98c22p0

theorem E98c22wire : entryWords E98c22 = E98c22words := by
  rfl

theorem E98c22wordBound : E98c22words.all wordBound = true := by
  simp only [E98c22words,List.all_append,E98c22p0bound]
  try rfl

theorem E98c22bounded : ∀ n ∈ E98c22words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c22wordBound

def E98c23 : Entry := ⟨3159, 17, [112,99,50,35,53,55], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 20 (0)) (.cons (.column 20 (-1)) .nil)) .nil)))))⟩

def E98c23p0 : List Nat := [3159,17,6,112,99,50,35,53,55,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,20,0,1,1,20,1,0,0]
theorem E98c23p0bound : E98c23p0.all wordBound = true := (by decide : [3159,17,6,112,99,50,35,53,55,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,20,0,1,1,20,1,0,0].all wordBound = true)

def E98c23words : List Nat := E98c23p0

theorem E98c23wire : entryWords E98c23 = E98c23words := by
  rfl

theorem E98c23wordBound : E98c23words.all wordBound = true := by
  simp only [E98c23words,List.all_append,E98c23p0bound]
  try rfl

theorem E98c23bounded : ∀ n ∈ E98c23words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c23wordBound

def E98c24 : Entry := ⟨3160, 17, [112,99,50,35,53,56], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.difference (.column 21 (0)) (.cons (.column 21 (-1)) .nil)) .nil))))⟩

def E98c24p0 : List Nat := [3160,17,6,112,99,50,35,53,56,0,17,0,0,16,4,1,1,440,0,1,3,1,21,0,1,1,21,1,0,0]
theorem E98c24p0bound : E98c24p0.all wordBound = true := (by decide : [3160,17,6,112,99,50,35,53,56,0,17,0,0,16,4,1,1,440,0,1,3,1,21,0,1,1,21,1,0,0].all wordBound = true)

def E98c24words : List Nat := E98c24p0

theorem E98c24wire : entryWords E98c24 = E98c24words := by
  rfl

theorem E98c24wordBound : E98c24words.all wordBound = true := by
  simp only [E98c24words,List.all_append,E98c24p0bound]
  try rfl

theorem E98c24bounded : ∀ n ∈ E98c24words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c24wordBound

def E98c25 : Entry := ⟨3161, 17, [112,99,50,35,53,57], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 22 (0)) (.cons (.column 22 (-1)) .nil)) .nil)))))⟩

def E98c25p0 : List Nat := [3161,17,6,112,99,50,35,53,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,22,0,1,1,22,1,0,0]
theorem E98c25p0bound : E98c25p0.all wordBound = true := (by decide : [3161,17,6,112,99,50,35,53,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,22,0,1,1,22,1,0,0].all wordBound = true)

def E98c25words : List Nat := E98c25p0

theorem E98c25wire : entryWords E98c25 = E98c25words := by
  rfl

theorem E98c25wordBound : E98c25words.all wordBound = true := by
  simp only [E98c25words,List.all_append,E98c25p0bound]
  try rfl

theorem E98c25bounded : ∀ n ∈ E98c25words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c25wordBound

def E98c26 : Entry := ⟨3162, 17, [112,99,50,35,54,48], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 23 (0)) (.cons (.column 23 (-1)) .nil)) .nil)))))⟩

def E98c26p0 : List Nat := [3162,17,6,112,99,50,35,54,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,23,0,1,1,23,1,0,0]
theorem E98c26p0bound : E98c26p0.all wordBound = true := (by decide : [3162,17,6,112,99,50,35,54,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,23,0,1,1,23,1,0,0].all wordBound = true)

def E98c26words : List Nat := E98c26p0

theorem E98c26wire : entryWords E98c26 = E98c26words := by
  rfl

theorem E98c26wordBound : E98c26words.all wordBound = true := by
  simp only [E98c26words,List.all_append,E98c26p0bound]
  try rfl

theorem E98c26bounded : ∀ n ∈ E98c26words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c26wordBound

def E98c27 : Entry := ⟨3163, 17, [112,99,50,35,54,49], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 24 (0)) (.cons (.column 24 (-1)) .nil)) .nil)))))⟩

def E98c27p0 : List Nat := [3163,17,6,112,99,50,35,54,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,24,0,1,1,24,1,0,0]
theorem E98c27p0bound : E98c27p0.all wordBound = true := (by decide : [3163,17,6,112,99,50,35,54,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,24,0,1,1,24,1,0,0].all wordBound = true)

def E98c27words : List Nat := E98c27p0

theorem E98c27wire : entryWords E98c27 = E98c27words := by
  rfl

theorem E98c27wordBound : E98c27words.all wordBound = true := by
  simp only [E98c27words,List.all_append,E98c27p0bound]
  try rfl

theorem E98c27bounded : ∀ n ∈ E98c27words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c27wordBound

def E98c28 : Entry := ⟨3164, 17, [112,99,50,35,54,50], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 25 (0)) (.cons (.column 25 (-1)) .nil)) .nil)))))⟩

def E98c28p0 : List Nat := [3164,17,6,112,99,50,35,54,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,25,0,1,1,25,1,0,0]
theorem E98c28p0bound : E98c28p0.all wordBound = true := (by decide : [3164,17,6,112,99,50,35,54,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,25,0,1,1,25,1,0,0].all wordBound = true)

def E98c28words : List Nat := E98c28p0

theorem E98c28wire : entryWords E98c28 = E98c28words := by
  rfl

theorem E98c28wordBound : E98c28words.all wordBound = true := by
  simp only [E98c28words,List.all_append,E98c28p0bound]
  try rfl

theorem E98c28bounded : ∀ n ∈ E98c28words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c28wordBound

def E98c29 : Entry := ⟨3165, 17, [112,99,50,35,54,51], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.difference (.column 26 (0)) (.cons (.column 26 (-1)) .nil)) .nil))))⟩

def E98c29p0 : List Nat := [3165,17,6,112,99,50,35,54,51,0,17,0,0,16,4,1,1,440,0,1,3,1,26,0,1,1,26,1,0,0]
theorem E98c29p0bound : E98c29p0.all wordBound = true := (by decide : [3165,17,6,112,99,50,35,54,51,0,17,0,0,16,4,1,1,440,0,1,3,1,26,0,1,1,26,1,0,0].all wordBound = true)

def E98c29words : List Nat := E98c29p0

theorem E98c29wire : entryWords E98c29 = E98c29words := by
  rfl

theorem E98c29wordBound : E98c29words.all wordBound = true := by
  simp only [E98c29words,List.all_append,E98c29p0bound]
  try rfl

theorem E98c29bounded : ∀ n ∈ E98c29words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c29wordBound

def E98c30 : Entry := ⟨3166, 17, [112,99,50,35,54,52], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 27 (0)) (.cons (.column 27 (-1)) .nil)) .nil)))))⟩

def E98c30p0 : List Nat := [3166,17,6,112,99,50,35,54,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,27,0,1,1,27,1,0,0]
theorem E98c30p0bound : E98c30p0.all wordBound = true := (by decide : [3166,17,6,112,99,50,35,54,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,27,0,1,1,27,1,0,0].all wordBound = true)

def E98c30words : List Nat := E98c30p0

theorem E98c30wire : entryWords E98c30 = E98c30words := by
  rfl

theorem E98c30wordBound : E98c30words.all wordBound = true := by
  simp only [E98c30words,List.all_append,E98c30p0bound]
  try rfl

theorem E98c30bounded : ∀ n ∈ E98c30words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c30wordBound

def E98c31 : Entry := ⟨3167, 17, [112,99,50,35,54,53], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 28 (0)) (.cons (.column 28 (-1)) .nil)) .nil)))))⟩

def E98c31p0 : List Nat := [3167,17,6,112,99,50,35,54,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,28,0,1,1,28,1,0,0]
theorem E98c31p0bound : E98c31p0.all wordBound = true := (by decide : [3167,17,6,112,99,50,35,54,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,28,0,1,1,28,1,0,0].all wordBound = true)

def E98c31words : List Nat := E98c31p0

theorem E98c31wire : entryWords E98c31 = E98c31words := by
  rfl

theorem E98c31wordBound : E98c31words.all wordBound = true := by
  simp only [E98c31words,List.all_append,E98c31p0bound]
  try rfl

theorem E98c31bounded : ∀ n ∈ E98c31words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E98c31wordBound

def E98 : List Entry := [E98c0,E98c1,E98c2,E98c3,E98c4,E98c5,E98c6,E98c7,E98c8,E98c9,E98c10,E98c11,E98c12,E98c13,E98c14,E98c15,E98c16,E98c17,E98c18,E98c19,E98c20,E98c21,E98c22,E98c23,E98c24,E98c25,E98c26,E98c27,E98c28,E98c29,E98c30,E98c31]

def E98words : List Nat := E98c0words ++ E98c1words ++ E98c2words ++ E98c3words ++ E98c4words ++ E98c5words ++ E98c6words ++ E98c7words ++ E98c8words ++ E98c9words ++ E98c10words ++ E98c11words ++ E98c12words ++ E98c13words ++ E98c14words ++ E98c15words ++ E98c16words ++ E98c17words ++ E98c18words ++ E98c19words ++ E98c20words ++ E98c21words ++ E98c22words ++ E98c23words ++ E98c24words ++ E98c25words ++ E98c26words ++ E98c27words ++ E98c28words ++ E98c29words ++ E98c30words ++ E98c31words

theorem E98wire : E98.flatMap entry.encode = E98words := by
  rw [entry_fast_fun]
  simp only [E98,List.flatMap_cons,List.flatMap_nil,List.append_nil,E98c0wire,E98c1wire,E98c2wire,E98c3wire,E98c4wire,E98c5wire,E98c6wire,E98c7wire,E98c8wire,E98c9wire,E98c10wire,E98c11wire,E98c12wire,E98c13wire,E98c14wire,E98c15wire,E98c16wire,E98c17wire,E98c18wire,E98c19wire,E98c20wire,E98c21wire,E98c22wire,E98c23wire,E98c24wire,E98c25wire,E98c26wire,E98c27wire,E98c28wire,E98c29wire,E98c30wire,E98c31wire]
  rfl

theorem E98wordBound : E98words.all wordBound = true := by
  simp only [E98words,List.all_append,E98c0wordBound,E98c1wordBound,E98c2wordBound,E98c3wordBound,E98c4wordBound,E98c5wordBound,E98c6wordBound,E98c7wordBound,E98c8wordBound,E98c9wordBound,E98c10wordBound,E98c11wordBound,E98c12wordBound,E98c13wordBound,E98c14wordBound,E98c15wordBound,E98c16wordBound,E98c17wordBound,E98c18wordBound,E98c19wordBound,E98c20wordBound,E98c21wordBound,E98c22wordBound,E98c23wordBound,E98c24wordBound,E98c25wordBound,E98c26wordBound,E98c27wordBound,E98c28wordBound,E98c29wordBound,E98c30wordBound,E98c31wordBound]
  decide

theorem E98bounded : ∀ n ∈ E98words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using E98wordBound

theorem E98length : E98.length = 32 := by rfl

def E98selected : List RawConstraint := []
theorem E98select : (E98.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).map Entry.rule = E98selected := by rfl

def E98incoming : List RawConstraint := []
theorem E98calls : (ArtifactBinding.incomingEntries ⟨[],E98⟩).map Entry.rule = E98incoming := by rfl

theorem E98closure : (E98.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).all (fun e => (ArtifactBinding.referencedModules e).all (fun id => decide (id ∈ ArtifactBinding.selectedIds))) = true := by decide

end DivRemFV.Replay
