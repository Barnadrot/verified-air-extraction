import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def E106c0 : Entry := ⟨3392, 17, [112,99,50,35,50,57,48], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 253 (0)) (.cons (.column 253 (-1)) .nil)) .nil)))))⟩

def E106c0p0 : List Nat := [3392,17,7,112,99,50,35,50,57,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,253,0,1,1,253,1,0,0]
theorem E106c0p0bound : E106c0p0.all wordBound = true := (by decide : [3392,17,7,112,99,50,35,50,57,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,253,0,1,1,253,1,0,0].all wordBound = true)

def E106c0words : List Nat := E106c0p0

theorem E106c0wire : entryWords E106c0 = E106c0words := by
  rfl

theorem E106c0wordBound : E106c0words.all wordBound = true := by
  simp only [E106c0words,List.all_append,E106c0p0bound]
  try rfl

theorem E106c0bounded : ∀ n ∈ E106c0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c0wordBound

def E106c1 : Entry := ⟨3393, 17, [112,99,50,35,50,57,49], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 254 (0)) (.cons (.column 254 (-1)) .nil)) .nil)))))⟩

def E106c1p0 : List Nat := [3393,17,7,112,99,50,35,50,57,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,254,0,1,1,254,1,0,0]
theorem E106c1p0bound : E106c1p0.all wordBound = true := (by decide : [3393,17,7,112,99,50,35,50,57,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,254,0,1,1,254,1,0,0].all wordBound = true)

def E106c1words : List Nat := E106c1p0

theorem E106c1wire : entryWords E106c1 = E106c1words := by
  rfl

theorem E106c1wordBound : E106c1words.all wordBound = true := by
  simp only [E106c1words,List.all_append,E106c1p0bound]
  try rfl

theorem E106c1bounded : ∀ n ∈ E106c1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c1wordBound

def E106c2 : Entry := ⟨3394, 17, [112,99,50,35,50,57,50], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 255 (0)) (.cons (.column 255 (-1)) .nil)) .nil)))))⟩

def E106c2p0 : List Nat := [3394,17,7,112,99,50,35,50,57,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,255,0,1,1,255,1,0,0]
theorem E106c2p0bound : E106c2p0.all wordBound = true := (by decide : [3394,17,7,112,99,50,35,50,57,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,255,0,1,1,255,1,0,0].all wordBound = true)

def E106c2words : List Nat := E106c2p0

theorem E106c2wire : entryWords E106c2 = E106c2words := by
  rfl

theorem E106c2wordBound : E106c2words.all wordBound = true := by
  simp only [E106c2words,List.all_append,E106c2p0bound]
  try rfl

theorem E106c2bounded : ∀ n ∈ E106c2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c2wordBound

def E106c3 : Entry := ⟨3395, 17, [112,99,50,35,50,57,51], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 256 (0)) (.cons (.column 256 (-1)) .nil)) .nil)))))⟩

def E106c3p0 : List Nat := [3395,17,7,112,99,50,35,50,57,51,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,256,0,1,1,256,1,0,0]
theorem E106c3p0bound : E106c3p0.all wordBound = true := (by decide : [3395,17,7,112,99,50,35,50,57,51,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,256,0,1,1,256,1,0,0].all wordBound = true)

def E106c3words : List Nat := E106c3p0

theorem E106c3wire : entryWords E106c3 = E106c3words := by
  rfl

theorem E106c3wordBound : E106c3words.all wordBound = true := by
  simp only [E106c3words,List.all_append,E106c3p0bound]
  try rfl

theorem E106c3bounded : ∀ n ∈ E106c3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c3wordBound

def E106c4 : Entry := ⟨3396, 17, [112,99,50,35,50,57,52], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 257 (0)) (.cons (.column 257 (-1)) .nil)) .nil)))))⟩

def E106c4p0 : List Nat := [3396,17,7,112,99,50,35,50,57,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,257,0,1,1,257,1,0,0]
theorem E106c4p0bound : E106c4p0.all wordBound = true := (by decide : [3396,17,7,112,99,50,35,50,57,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,257,0,1,1,257,1,0,0].all wordBound = true)

def E106c4words : List Nat := E106c4p0

theorem E106c4wire : entryWords E106c4 = E106c4words := by
  rfl

theorem E106c4wordBound : E106c4words.all wordBound = true := by
  simp only [E106c4words,List.all_append,E106c4p0bound]
  try rfl

theorem E106c4bounded : ∀ n ∈ E106c4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c4wordBound

def E106c5 : Entry := ⟨3397, 17, [112,99,50,35,50,57,53], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 258 (0)) (.cons (.column 258 (-1)) .nil)) .nil)))))⟩

def E106c5p0 : List Nat := [3397,17,7,112,99,50,35,50,57,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,258,0,1,1,258,1,0,0]
theorem E106c5p0bound : E106c5p0.all wordBound = true := (by decide : [3397,17,7,112,99,50,35,50,57,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,258,0,1,1,258,1,0,0].all wordBound = true)

def E106c5words : List Nat := E106c5p0

theorem E106c5wire : entryWords E106c5 = E106c5words := by
  rfl

theorem E106c5wordBound : E106c5words.all wordBound = true := by
  simp only [E106c5words,List.all_append,E106c5p0bound]
  try rfl

theorem E106c5bounded : ∀ n ∈ E106c5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c5wordBound

def E106c6 : Entry := ⟨3398, 17, [112,99,50,35,50,57,54], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 259 (0)) (.cons (.column 259 (-1)) .nil)) .nil)))))⟩

def E106c6p0 : List Nat := [3398,17,7,112,99,50,35,50,57,54,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,259,0,1,1,259,1,0,0]
theorem E106c6p0bound : E106c6p0.all wordBound = true := (by decide : [3398,17,7,112,99,50,35,50,57,54,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,259,0,1,1,259,1,0,0].all wordBound = true)

def E106c6words : List Nat := E106c6p0

theorem E106c6wire : entryWords E106c6 = E106c6words := by
  rfl

theorem E106c6wordBound : E106c6words.all wordBound = true := by
  simp only [E106c6words,List.all_append,E106c6p0bound]
  try rfl

theorem E106c6bounded : ∀ n ∈ E106c6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c6wordBound

def E106c7 : Entry := ⟨3399, 17, [112,99,50,35,50,57,55], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 260 (0)) (.cons (.column 260 (-1)) .nil)) .nil)))))⟩

def E106c7p0 : List Nat := [3399,17,7,112,99,50,35,50,57,55,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,260,0,1,1,260,1,0,0]
theorem E106c7p0bound : E106c7p0.all wordBound = true := (by decide : [3399,17,7,112,99,50,35,50,57,55,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,260,0,1,1,260,1,0,0].all wordBound = true)

def E106c7words : List Nat := E106c7p0

theorem E106c7wire : entryWords E106c7 = E106c7words := by
  rfl

theorem E106c7wordBound : E106c7words.all wordBound = true := by
  simp only [E106c7words,List.all_append,E106c7p0bound]
  try rfl

theorem E106c7bounded : ∀ n ∈ E106c7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c7wordBound

def E106c8 : Entry := ⟨3400, 17, [112,99,50,35,50,57,56], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 261 (0)) (.cons (.column 261 (-1)) .nil)) .nil)))))⟩

def E106c8p0 : List Nat := [3400,17,7,112,99,50,35,50,57,56,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,261,0,1,1,261,1,0,0]
theorem E106c8p0bound : E106c8p0.all wordBound = true := (by decide : [3400,17,7,112,99,50,35,50,57,56,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,261,0,1,1,261,1,0,0].all wordBound = true)

def E106c8words : List Nat := E106c8p0

theorem E106c8wire : entryWords E106c8 = E106c8words := by
  rfl

theorem E106c8wordBound : E106c8words.all wordBound = true := by
  simp only [E106c8words,List.all_append,E106c8p0bound]
  try rfl

theorem E106c8bounded : ∀ n ∈ E106c8words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c8wordBound

def E106c9 : Entry := ⟨3401, 17, [112,99,50,35,50,57,57], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 262 (0)) (.cons (.column 262 (-1)) .nil)) .nil)))))⟩

def E106c9p0 : List Nat := [3401,17,7,112,99,50,35,50,57,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,262,0,1,1,262,1,0,0]
theorem E106c9p0bound : E106c9p0.all wordBound = true := (by decide : [3401,17,7,112,99,50,35,50,57,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,262,0,1,1,262,1,0,0].all wordBound = true)

def E106c9words : List Nat := E106c9p0

theorem E106c9wire : entryWords E106c9 = E106c9words := by
  rfl

theorem E106c9wordBound : E106c9words.all wordBound = true := by
  simp only [E106c9words,List.all_append,E106c9p0bound]
  try rfl

theorem E106c9bounded : ∀ n ∈ E106c9words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c9wordBound

def E106c10 : Entry := ⟨3402, 17, [112,99,50,35,51,48,48], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 263 (0)) (.cons (.column 263 (-1)) .nil)) .nil)))))⟩

def E106c10p0 : List Nat := [3402,17,7,112,99,50,35,51,48,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,263,0,1,1,263,1,0,0]
theorem E106c10p0bound : E106c10p0.all wordBound = true := (by decide : [3402,17,7,112,99,50,35,51,48,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,263,0,1,1,263,1,0,0].all wordBound = true)

def E106c10words : List Nat := E106c10p0

theorem E106c10wire : entryWords E106c10 = E106c10words := by
  rfl

theorem E106c10wordBound : E106c10words.all wordBound = true := by
  simp only [E106c10words,List.all_append,E106c10p0bound]
  try rfl

theorem E106c10bounded : ∀ n ∈ E106c10words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c10wordBound

def E106c11 : Entry := ⟨3403, 17, [112,99,50,35,51,48,49], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 264 (0)) (.cons (.column 264 (-1)) .nil)) .nil)))))⟩

def E106c11p0 : List Nat := [3403,17,7,112,99,50,35,51,48,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,264,0,1,1,264,1,0,0]
theorem E106c11p0bound : E106c11p0.all wordBound = true := (by decide : [3403,17,7,112,99,50,35,51,48,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,264,0,1,1,264,1,0,0].all wordBound = true)

def E106c11words : List Nat := E106c11p0

theorem E106c11wire : entryWords E106c11 = E106c11words := by
  rfl

theorem E106c11wordBound : E106c11words.all wordBound = true := by
  simp only [E106c11words,List.all_append,E106c11p0bound]
  try rfl

theorem E106c11bounded : ∀ n ∈ E106c11words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c11wordBound

def E106c12 : Entry := ⟨3404, 17, [112,99,50,35,51,48,50], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 265 (0)) (.cons (.column 265 (-1)) .nil)) .nil)))))⟩

def E106c12p0 : List Nat := [3404,17,7,112,99,50,35,51,48,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,265,0,1,1,265,1,0,0]
theorem E106c12p0bound : E106c12p0.all wordBound = true := (by decide : [3404,17,7,112,99,50,35,51,48,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,265,0,1,1,265,1,0,0].all wordBound = true)

def E106c12words : List Nat := E106c12p0

theorem E106c12wire : entryWords E106c12 = E106c12words := by
  rfl

theorem E106c12wordBound : E106c12words.all wordBound = true := by
  simp only [E106c12words,List.all_append,E106c12p0bound]
  try rfl

theorem E106c12bounded : ∀ n ∈ E106c12words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c12wordBound

def E106c13 : Entry := ⟨3405, 17, [112,99,50,35,51,48,51], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 266 (0)) (.cons (.column 266 (-1)) .nil)) .nil)))))⟩

def E106c13p0 : List Nat := [3405,17,7,112,99,50,35,51,48,51,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,266,0,1,1,266,1,0,0]
theorem E106c13p0bound : E106c13p0.all wordBound = true := (by decide : [3405,17,7,112,99,50,35,51,48,51,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,266,0,1,1,266,1,0,0].all wordBound = true)

def E106c13words : List Nat := E106c13p0

theorem E106c13wire : entryWords E106c13 = E106c13words := by
  rfl

theorem E106c13wordBound : E106c13words.all wordBound = true := by
  simp only [E106c13words,List.all_append,E106c13p0bound]
  try rfl

theorem E106c13bounded : ∀ n ∈ E106c13words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c13wordBound

def E106c14 : Entry := ⟨3406, 17, [112,99,50,35,51,48,52], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 267 (0)) (.cons (.column 267 (-1)) .nil)) .nil)))))⟩

def E106c14p0 : List Nat := [3406,17,7,112,99,50,35,51,48,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,267,0,1,1,267,1,0,0]
theorem E106c14p0bound : E106c14p0.all wordBound = true := (by decide : [3406,17,7,112,99,50,35,51,48,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,267,0,1,1,267,1,0,0].all wordBound = true)

def E106c14words : List Nat := E106c14p0

theorem E106c14wire : entryWords E106c14 = E106c14words := by
  rfl

theorem E106c14wordBound : E106c14words.all wordBound = true := by
  simp only [E106c14words,List.all_append,E106c14p0bound]
  try rfl

theorem E106c14bounded : ∀ n ∈ E106c14words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c14wordBound

def E106c15 : Entry := ⟨3407, 17, [112,99,50,35,51,48,53], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 268 (0)) (.cons (.column 268 (-1)) .nil)) .nil)))))⟩

def E106c15p0 : List Nat := [3407,17,7,112,99,50,35,51,48,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,268,0,1,1,268,1,0,0]
theorem E106c15p0bound : E106c15p0.all wordBound = true := (by decide : [3407,17,7,112,99,50,35,51,48,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,268,0,1,1,268,1,0,0].all wordBound = true)

def E106c15words : List Nat := E106c15p0

theorem E106c15wire : entryWords E106c15 = E106c15words := by
  rfl

theorem E106c15wordBound : E106c15words.all wordBound = true := by
  simp only [E106c15words,List.all_append,E106c15p0bound]
  try rfl

theorem E106c15bounded : ∀ n ∈ E106c15words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c15wordBound

def E106c16 : Entry := ⟨3408, 17, [112,99,50,35,51,48,54], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 269 (0)) (.cons (.column 269 (-1)) .nil)) .nil)))))⟩

def E106c16p0 : List Nat := [3408,17,7,112,99,50,35,51,48,54,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,269,0,1,1,269,1,0,0]
theorem E106c16p0bound : E106c16p0.all wordBound = true := (by decide : [3408,17,7,112,99,50,35,51,48,54,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,269,0,1,1,269,1,0,0].all wordBound = true)

def E106c16words : List Nat := E106c16p0

theorem E106c16wire : entryWords E106c16 = E106c16words := by
  rfl

theorem E106c16wordBound : E106c16words.all wordBound = true := by
  simp only [E106c16words,List.all_append,E106c16p0bound]
  try rfl

theorem E106c16bounded : ∀ n ∈ E106c16words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c16wordBound

def E106c17 : Entry := ⟨3409, 17, [112,99,50,35,51,48,55], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 270 (0)) (.cons (.column 270 (-1)) .nil)) .nil)))))⟩

def E106c17p0 : List Nat := [3409,17,7,112,99,50,35,51,48,55,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,270,0,1,1,270,1,0,0]
theorem E106c17p0bound : E106c17p0.all wordBound = true := (by decide : [3409,17,7,112,99,50,35,51,48,55,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,270,0,1,1,270,1,0,0].all wordBound = true)

def E106c17words : List Nat := E106c17p0

theorem E106c17wire : entryWords E106c17 = E106c17words := by
  rfl

theorem E106c17wordBound : E106c17words.all wordBound = true := by
  simp only [E106c17words,List.all_append,E106c17p0bound]
  try rfl

theorem E106c17bounded : ∀ n ∈ E106c17words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c17wordBound

def E106c18 : Entry := ⟨3410, 17, [112,99,50,35,51,48,56], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 271 (0)) (.cons (.column 271 (-1)) .nil)) .nil)))))⟩

def E106c18p0 : List Nat := [3410,17,7,112,99,50,35,51,48,56,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,271,0,1,1,271,1,0,0]
theorem E106c18p0bound : E106c18p0.all wordBound = true := (by decide : [3410,17,7,112,99,50,35,51,48,56,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,271,0,1,1,271,1,0,0].all wordBound = true)

def E106c18words : List Nat := E106c18p0

theorem E106c18wire : entryWords E106c18 = E106c18words := by
  rfl

theorem E106c18wordBound : E106c18words.all wordBound = true := by
  simp only [E106c18words,List.all_append,E106c18p0bound]
  try rfl

theorem E106c18bounded : ∀ n ∈ E106c18words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c18wordBound

def E106c19 : Entry := ⟨3411, 17, [112,99,50,35,51,48,57], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 272 (0)) (.cons (.column 272 (-1)) .nil)) .nil)))))⟩

def E106c19p0 : List Nat := [3411,17,7,112,99,50,35,51,48,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,272,0,1,1,272,1,0,0]
theorem E106c19p0bound : E106c19p0.all wordBound = true := (by decide : [3411,17,7,112,99,50,35,51,48,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,272,0,1,1,272,1,0,0].all wordBound = true)

def E106c19words : List Nat := E106c19p0

theorem E106c19wire : entryWords E106c19 = E106c19words := by
  rfl

theorem E106c19wordBound : E106c19words.all wordBound = true := by
  simp only [E106c19words,List.all_append,E106c19p0bound]
  try rfl

theorem E106c19bounded : ∀ n ∈ E106c19words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c19wordBound

def E106c20 : Entry := ⟨3412, 17, [112,99,50,35,51,49,48], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 273 (0)) (.cons (.column 273 (-1)) .nil)) .nil)))))⟩

def E106c20p0 : List Nat := [3412,17,7,112,99,50,35,51,49,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,273,0,1,1,273,1,0,0]
theorem E106c20p0bound : E106c20p0.all wordBound = true := (by decide : [3412,17,7,112,99,50,35,51,49,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,273,0,1,1,273,1,0,0].all wordBound = true)

def E106c20words : List Nat := E106c20p0

theorem E106c20wire : entryWords E106c20 = E106c20words := by
  rfl

theorem E106c20wordBound : E106c20words.all wordBound = true := by
  simp only [E106c20words,List.all_append,E106c20p0bound]
  try rfl

theorem E106c20bounded : ∀ n ∈ E106c20words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c20wordBound

def E106c21 : Entry := ⟨3413, 17, [112,99,50,35,51,49,49], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 274 (0)) (.cons (.column 274 (-1)) .nil)) .nil)))))⟩

def E106c21p0 : List Nat := [3413,17,7,112,99,50,35,51,49,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,274,0,1,1,274,1,0,0]
theorem E106c21p0bound : E106c21p0.all wordBound = true := (by decide : [3413,17,7,112,99,50,35,51,49,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,274,0,1,1,274,1,0,0].all wordBound = true)

def E106c21words : List Nat := E106c21p0

theorem E106c21wire : entryWords E106c21 = E106c21words := by
  rfl

theorem E106c21wordBound : E106c21words.all wordBound = true := by
  simp only [E106c21words,List.all_append,E106c21p0bound]
  try rfl

theorem E106c21bounded : ∀ n ∈ E106c21words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c21wordBound

def E106c22 : Entry := ⟨3414, 17, [112,99,50,35,51,49,50], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 275 (0)) (.cons (.column 275 (-1)) .nil)) .nil)))))⟩

def E106c22p0 : List Nat := [3414,17,7,112,99,50,35,51,49,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,275,0,1,1,275,1,0,0]
theorem E106c22p0bound : E106c22p0.all wordBound = true := (by decide : [3414,17,7,112,99,50,35,51,49,50,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,275,0,1,1,275,1,0,0].all wordBound = true)

def E106c22words : List Nat := E106c22p0

theorem E106c22wire : entryWords E106c22 = E106c22words := by
  rfl

theorem E106c22wordBound : E106c22words.all wordBound = true := by
  simp only [E106c22words,List.all_append,E106c22p0bound]
  try rfl

theorem E106c22bounded : ∀ n ∈ E106c22words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c22wordBound

def E106c23 : Entry := ⟨3415, 17, [112,99,50,35,51,49,51], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 276 (0)) (.cons (.column 276 (-1)) .nil)) .nil)))))⟩

def E106c23p0 : List Nat := [3415,17,7,112,99,50,35,51,49,51,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,276,0,1,1,276,1,0,0]
theorem E106c23p0bound : E106c23p0.all wordBound = true := (by decide : [3415,17,7,112,99,50,35,51,49,51,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,276,0,1,1,276,1,0,0].all wordBound = true)

def E106c23words : List Nat := E106c23p0

theorem E106c23wire : entryWords E106c23 = E106c23words := by
  rfl

theorem E106c23wordBound : E106c23words.all wordBound = true := by
  simp only [E106c23words,List.all_append,E106c23p0bound]
  try rfl

theorem E106c23bounded : ∀ n ∈ E106c23words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c23wordBound

def E106c24 : Entry := ⟨3416, 17, [112,99,50,35,51,49,52], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 277 (0)) (.cons (.column 277 (-1)) .nil)) .nil)))))⟩

def E106c24p0 : List Nat := [3416,17,7,112,99,50,35,51,49,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,277,0,1,1,277,1,0,0]
theorem E106c24p0bound : E106c24p0.all wordBound = true := (by decide : [3416,17,7,112,99,50,35,51,49,52,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,277,0,1,1,277,1,0,0].all wordBound = true)

def E106c24words : List Nat := E106c24p0

theorem E106c24wire : entryWords E106c24 = E106c24words := by
  rfl

theorem E106c24wordBound : E106c24words.all wordBound = true := by
  simp only [E106c24words,List.all_append,E106c24p0bound]
  try rfl

theorem E106c24bounded : ∀ n ∈ E106c24words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c24wordBound

def E106c25 : Entry := ⟨3417, 17, [112,99,50,35,51,49,53], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 278 (0)) (.cons (.column 278 (-1)) .nil)) .nil)))))⟩

def E106c25p0 : List Nat := [3417,17,7,112,99,50,35,51,49,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,278,0,1,1,278,1,0,0]
theorem E106c25p0bound : E106c25p0.all wordBound = true := (by decide : [3417,17,7,112,99,50,35,51,49,53,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,278,0,1,1,278,1,0,0].all wordBound = true)

def E106c25words : List Nat := E106c25p0

theorem E106c25wire : entryWords E106c25 = E106c25words := by
  rfl

theorem E106c25wordBound : E106c25words.all wordBound = true := by
  simp only [E106c25words,List.all_append,E106c25p0bound]
  try rfl

theorem E106c25bounded : ∀ n ∈ E106c25words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c25wordBound

def E106c26 : Entry := ⟨3418, 17, [112,99,50,35,51,49,54], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 279 (0)) (.cons (.column 279 (-1)) .nil)) .nil)))))⟩

def E106c26p0 : List Nat := [3418,17,7,112,99,50,35,51,49,54,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,279,0,1,1,279,1,0,0]
theorem E106c26p0bound : E106c26p0.all wordBound = true := (by decide : [3418,17,7,112,99,50,35,51,49,54,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,279,0,1,1,279,1,0,0].all wordBound = true)

def E106c26words : List Nat := E106c26p0

theorem E106c26wire : entryWords E106c26 = E106c26words := by
  rfl

theorem E106c26wordBound : E106c26words.all wordBound = true := by
  simp only [E106c26words,List.all_append,E106c26p0bound]
  try rfl

theorem E106c26bounded : ∀ n ∈ E106c26words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c26wordBound

def E106c27 : Entry := ⟨3419, 17, [112,99,50,35,51,49,55], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 280 (0)) (.cons (.column 280 (-1)) .nil)) .nil)))))⟩

def E106c27p0 : List Nat := [3419,17,7,112,99,50,35,51,49,55,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,280,0,1,1,280,1,0,0]
theorem E106c27p0bound : E106c27p0.all wordBound = true := (by decide : [3419,17,7,112,99,50,35,51,49,55,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,280,0,1,1,280,1,0,0].all wordBound = true)

def E106c27words : List Nat := E106c27p0

theorem E106c27wire : entryWords E106c27 = E106c27words := by
  rfl

theorem E106c27wordBound : E106c27words.all wordBound = true := by
  simp only [E106c27words,List.all_append,E106c27p0bound]
  try rfl

theorem E106c27bounded : ∀ n ∈ E106c27words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c27wordBound

def E106c28 : Entry := ⟨3420, 17, [112,99,50,35,51,49,56], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 281 (0)) (.cons (.column 281 (-1)) .nil)) .nil)))))⟩

def E106c28p0 : List Nat := [3420,17,7,112,99,50,35,51,49,56,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,281,0,1,1,281,1,0,0]
theorem E106c28p0bound : E106c28p0.all wordBound = true := (by decide : [3420,17,7,112,99,50,35,51,49,56,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,281,0,1,1,281,1,0,0].all wordBound = true)

def E106c28words : List Nat := E106c28p0

theorem E106c28wire : entryWords E106c28 = E106c28words := by
  rfl

theorem E106c28wordBound : E106c28words.all wordBound = true := by
  simp only [E106c28words,List.all_append,E106c28p0bound]
  try rfl

theorem E106c28bounded : ∀ n ∈ E106c28words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c28wordBound

def E106c29 : Entry := ⟨3421, 17, [112,99,50,35,51,49,57], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 282 (0)) (.cons (.column 282 (-1)) .nil)) .nil)))))⟩

def E106c29p0 : List Nat := [3421,17,7,112,99,50,35,51,49,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,282,0,1,1,282,1,0,0]
theorem E106c29p0bound : E106c29p0.all wordBound = true := (by decide : [3421,17,7,112,99,50,35,51,49,57,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,282,0,1,1,282,1,0,0].all wordBound = true)

def E106c29words : List Nat := E106c29p0

theorem E106c29wire : entryWords E106c29 = E106c29words := by
  rfl

theorem E106c29wordBound : E106c29words.all wordBound = true := by
  simp only [E106c29words,List.all_append,E106c29p0bound]
  try rfl

theorem E106c29bounded : ∀ n ∈ E106c29words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c29wordBound

def E106c30 : Entry := ⟨3422, 17, [112,99,50,35,51,50,48], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 283 (0)) (.cons (.column 283 (-1)) .nil)) .nil)))))⟩

def E106c30p0 : List Nat := [3422,17,7,112,99,50,35,51,50,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,283,0,1,1,283,1,0,0]
theorem E106c30p0bound : E106c30p0.all wordBound = true := (by decide : [3422,17,7,112,99,50,35,51,50,48,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,283,0,1,1,283,1,0,0].all wordBound = true)

def E106c30words : List Nat := E106c30p0

theorem E106c30wire : entryWords E106c30 = E106c30words := by
  rfl

theorem E106c30wordBound : E106c30words.all wordBound = true := by
  simp only [E106c30words,List.all_append,E106c30p0bound]
  try rfl

theorem E106c30bounded : ∀ n ∈ E106c30words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c30wordBound

def E106c31 : Entry := ⟨3423, 17, [112,99,50,35,51,50,49], (.vanishing 17 none (.product (.cons (.column 440 (0)) (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 297 (0)) .nil)) (.cons (.column 295 (0)) .nil))) (.cons (.difference (.column 284 (0)) (.cons (.column 284 (-1)) .nil)) .nil)))))⟩

def E106c31p0 : List Nat := [3423,17,7,112,99,50,35,51,50,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,284,0,1,1,284,1,0,0]
theorem E106c31p0bound : E106c31p0.all wordBound = true := (by decide : [3423,17,7,112,99,50,35,51,50,49,0,17,0,0,32,4,1,1,440,0,1,2,1,3,0,1,1,1,297,0,0,1,1,295,0,0,1,3,1,284,0,1,1,284,1,0,0].all wordBound = true)

def E106c31words : List Nat := E106c31p0

theorem E106c31wire : entryWords E106c31 = E106c31words := by
  rfl

theorem E106c31wordBound : E106c31words.all wordBound = true := by
  simp only [E106c31words,List.all_append,E106c31p0bound]
  try rfl

theorem E106c31bounded : ∀ n ∈ E106c31words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E106c31wordBound

def E106 : List Entry := [E106c0,E106c1,E106c2,E106c3,E106c4,E106c5,E106c6,E106c7,E106c8,E106c9,E106c10,E106c11,E106c12,E106c13,E106c14,E106c15,E106c16,E106c17,E106c18,E106c19,E106c20,E106c21,E106c22,E106c23,E106c24,E106c25,E106c26,E106c27,E106c28,E106c29,E106c30,E106c31]

def E106words : List Nat := E106c0words ++ E106c1words ++ E106c2words ++ E106c3words ++ E106c4words ++ E106c5words ++ E106c6words ++ E106c7words ++ E106c8words ++ E106c9words ++ E106c10words ++ E106c11words ++ E106c12words ++ E106c13words ++ E106c14words ++ E106c15words ++ E106c16words ++ E106c17words ++ E106c18words ++ E106c19words ++ E106c20words ++ E106c21words ++ E106c22words ++ E106c23words ++ E106c24words ++ E106c25words ++ E106c26words ++ E106c27words ++ E106c28words ++ E106c29words ++ E106c30words ++ E106c31words

theorem E106wire : E106.flatMap entry.encode = E106words := by
  rw [entry_fast_fun]
  simp only [E106,List.flatMap_cons,List.flatMap_nil,List.append_nil,E106c0wire,E106c1wire,E106c2wire,E106c3wire,E106c4wire,E106c5wire,E106c6wire,E106c7wire,E106c8wire,E106c9wire,E106c10wire,E106c11wire,E106c12wire,E106c13wire,E106c14wire,E106c15wire,E106c16wire,E106c17wire,E106c18wire,E106c19wire,E106c20wire,E106c21wire,E106c22wire,E106c23wire,E106c24wire,E106c25wire,E106c26wire,E106c27wire,E106c28wire,E106c29wire,E106c30wire,E106c31wire]
  rfl

theorem E106wordBound : E106words.all wordBound = true := by
  simp only [E106words,List.all_append,E106c0wordBound,E106c1wordBound,E106c2wordBound,E106c3wordBound,E106c4wordBound,E106c5wordBound,E106c6wordBound,E106c7wordBound,E106c8wordBound,E106c9wordBound,E106c10wordBound,E106c11wordBound,E106c12wordBound,E106c13wordBound,E106c14wordBound,E106c15wordBound,E106c16wordBound,E106c17wordBound,E106c18wordBound,E106c19wordBound,E106c20wordBound,E106c21wordBound,E106c22wordBound,E106c23wordBound,E106c24wordBound,E106c25wordBound,E106c26wordBound,E106c27wordBound,E106c28wordBound,E106c29wordBound,E106c30wordBound,E106c31wordBound]
  decide

theorem E106bounded : ∀ n ∈ E106words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using E106wordBound

theorem E106length : E106.length = 32 := by rfl

def E106selected : List RawConstraint := []
theorem E106select : (E106.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).map Entry.rule = E106selected := by rfl

def E106incoming : List RawConstraint := []
theorem E106calls : (ArtifactBinding.incomingEntries ⟨[],E106⟩).map Entry.rule = E106incoming := by rfl

theorem E106closure : (E106.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).all (fun e => (ArtifactBinding.referencedModules e).all (fun id => decide (id ∈ ArtifactBinding.selectedIds))) = true := by decide

end DivRemFV.Replay
