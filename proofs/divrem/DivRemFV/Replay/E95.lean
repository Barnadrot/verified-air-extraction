import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def E95c0 : Entry := ⟨3040, 17, [112,99,49,35,57,53], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 295 (0)) (.cons (.difference (.column 237 (0)) (.cons (.column 5 (0)) (.cons (.constant ⟨1, by decide⟩) .nil))) .nil)))))⟩

def E95c0p0 : List Nat := [3040,17,6,112,99,49,35,57,53,0,17,0,0,23,4,1,1,439,0,1,1,295,0,1,3,1,237,0,1,1,5,0,1,0,1,0,0]
theorem E95c0p0bound : E95c0p0.all wordBound = true := (by decide : [3040,17,6,112,99,49,35,57,53,0,17,0,0,23,4,1,1,439,0,1,1,295,0,1,3,1,237,0,1,1,5,0,1,0,1,0,0].all wordBound = true)

def E95c0words : List Nat := E95c0p0

theorem E95c0wire : entryWords E95c0 = E95c0words := by
  rfl

theorem E95c0wordBound : E95c0words.all wordBound = true := by
  simp only [E95c0words,List.all_append,E95c0p0bound]
  try rfl

theorem E95c0bounded : ∀ n ∈ E95c0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c0wordBound

def E95c1 : Entry := ⟨3041, 17, [112,99,49,35,57,54], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 295 (0)) (.cons (.difference (.column 235 (0)) (.cons (.column 236 (0)) (.cons (.constant ⟨80, by decide⟩) .nil))) .nil)))))⟩

def E95c1p0 : List Nat := [3041,17,6,112,99,49,35,57,54,0,17,0,0,23,4,1,1,439,0,1,1,295,0,1,3,1,235,0,1,1,236,0,1,0,80,0,0]
theorem E95c1p0bound : E95c1p0.all wordBound = true := (by decide : [3041,17,6,112,99,49,35,57,54,0,17,0,0,23,4,1,1,439,0,1,1,295,0,1,3,1,235,0,1,1,236,0,1,0,80,0,0].all wordBound = true)

def E95c1words : List Nat := E95c1p0

theorem E95c1wire : entryWords E95c1 = E95c1words := by
  rfl

theorem E95c1wordBound : E95c1words.all wordBound = true := by
  simp only [E95c1words,List.all_append,E95c1p0bound]
  try rfl

theorem E95c1bounded : ∀ n ∈ E95c1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c1wordBound

def E95c2 : Entry := ⟨3042, 17, [112,99,49,35,57,55], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 295 (0)) (.cons (.difference (.sum (.cons (.column 240 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 297 (0)) .nil))) .nil))) (.cons (.column 357 (0)) (.cons (.constant ⟨1, by decide⟩) .nil))) .nil)))))⟩

def E95c2p0 : List Nat := [3042,17,6,112,99,49,35,57,55,0,17,0,0,36,4,1,1,439,0,1,1,295,0,1,3,2,1,1,240,0,1,4,1,0,65536,1,1,297,0,0,0,1,1,357,0,1,0,1,0,0]
theorem E95c2p0bound : E95c2p0.all wordBound = true := (by decide : [3042,17,6,112,99,49,35,57,55,0,17,0,0,36,4,1,1,439,0,1,1,295,0,1,3,2,1,1,240,0,1,4,1,0,65536,1,1,297,0,0,0,1,1,357,0,1,0,1,0,0].all wordBound = true)

def E95c2words : List Nat := E95c2p0

theorem E95c2wire : entryWords E95c2 = E95c2words := by
  rfl

theorem E95c2wordBound : E95c2words.all wordBound = true := by
  simp only [E95c2words,List.all_append,E95c2p0bound]
  try rfl

theorem E95c2bounded : ∀ n ∈ E95c2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c2wordBound

def E95c3 : Entry := ⟨3043, 17, [112,99,49,35,57,56], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 295 (0)) (.cons (.difference (.column 239 (0)) (.cons (.column 356 (0)) (.cons (.column 297 (0)) .nil))) .nil)))))⟩

def E95c3p0 : List Nat := [3043,17,6,112,99,49,35,57,56,0,17,0,0,24,4,1,1,439,0,1,1,295,0,1,3,1,239,0,1,1,356,0,1,1,297,0,0,0]
theorem E95c3p0bound : E95c3p0.all wordBound = true := (by decide : [3043,17,6,112,99,49,35,57,56,0,17,0,0,24,4,1,1,439,0,1,1,295,0,1,3,1,239,0,1,1,356,0,1,1,297,0,0,0].all wordBound = true)

def E95c3words : List Nat := E95c3p0

theorem E95c3wire : entryWords E95c3 = E95c3words := by
  rfl

theorem E95c3wordBound : E95c3words.all wordBound = true := by
  simp only [E95c3words,List.all_append,E95c3p0bound]
  try rfl

theorem E95c3bounded : ∀ n ∈ E95c3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c3wordBound

def E95c4 : Entry := ⟨3044, 17, [112,99,49,35,57,57], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 295 (0)) (.cons (.difference (.column 238 (0)) (.cons (.constant ⟨1, by decide⟩) .nil)) .nil)))))⟩

def E95c4p0 : List Nat := [3044,17,6,112,99,49,35,57,57,0,17,0,0,19,4,1,1,439,0,1,1,295,0,1,3,1,238,0,1,0,1,0,0]
theorem E95c4p0bound : E95c4p0.all wordBound = true := (by decide : [3044,17,6,112,99,49,35,57,57,0,17,0,0,19,4,1,1,439,0,1,1,295,0,1,3,1,238,0,1,0,1,0,0].all wordBound = true)

def E95c4words : List Nat := E95c4p0

theorem E95c4wire : entryWords E95c4 = E95c4words := by
  rfl

theorem E95c4wordBound : E95c4words.all wordBound = true := by
  simp only [E95c4words,List.all_append,E95c4p0bound]
  try rfl

theorem E95c4bounded : ∀ n ∈ E95c4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c4wordBound

def E95c5 : Entry := ⟨3045, 17, [112,99,49,35,49,48,48], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 295 (0)) (.cons (.difference (.sum (.cons (.column 242 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 416 (0)) .nil))) .nil))) (.cons (.column 357 (0)) (.cons (.constant ⟨2, by decide⟩) .nil))) .nil)))))⟩

def E95c5p0 : List Nat := [3045,17,7,112,99,49,35,49,48,48,0,17,0,0,36,4,1,1,439,0,1,1,295,0,1,3,2,1,1,242,0,1,4,1,0,65536,1,1,416,0,0,0,1,1,357,0,1,0,2,0,0]
theorem E95c5p0bound : E95c5p0.all wordBound = true := (by decide : [3045,17,7,112,99,49,35,49,48,48,0,17,0,0,36,4,1,1,439,0,1,1,295,0,1,3,2,1,1,242,0,1,4,1,0,65536,1,1,416,0,0,0,1,1,357,0,1,0,2,0,0].all wordBound = true)

def E95c5words : List Nat := E95c5p0

theorem E95c5wire : entryWords E95c5 = E95c5words := by
  rfl

theorem E95c5wordBound : E95c5words.all wordBound = true := by
  simp only [E95c5words,List.all_append,E95c5p0bound]
  try rfl

theorem E95c5bounded : ∀ n ∈ E95c5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c5wordBound

def E95c6 : Entry := ⟨3046, 17, [112,99,49,35,49,48,49], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 295 (0)) (.cons (.difference (.column 241 (0)) (.cons (.column 356 (0)) (.cons (.column 416 (0)) .nil))) .nil)))))⟩

def E95c6p0 : List Nat := [3046,17,7,112,99,49,35,49,48,49,0,17,0,0,24,4,1,1,439,0,1,1,295,0,1,3,1,241,0,1,1,356,0,1,1,416,0,0,0]
theorem E95c6p0bound : E95c6p0.all wordBound = true := (by decide : [3046,17,7,112,99,49,35,49,48,49,0,17,0,0,24,4,1,1,439,0,1,1,295,0,1,3,1,241,0,1,1,356,0,1,1,416,0,0,0].all wordBound = true)

def E95c6words : List Nat := E95c6p0

theorem E95c6wire : entryWords E95c6 = E95c6words := by
  rfl

theorem E95c6wordBound : E95c6words.all wordBound = true := by
  simp only [E95c6words,List.all_append,E95c6p0bound]
  try rfl

theorem E95c6bounded : ∀ n ∈ E95c6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c6wordBound

def E95c7 : Entry := ⟨3047, 17, [112,99,49,35,49,48,50], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 295 (0)) (.cons (.difference (.sum (.cons (.column 3 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 417 (0)) .nil))) .nil))) (.cons (.column 357 (0)) (.cons (.constant ⟨3, by decide⟩) .nil))) .nil)))))⟩

def E95c7p0 : List Nat := [3047,17,7,112,99,49,35,49,48,50,0,17,0,0,36,4,1,1,439,0,1,1,295,0,1,3,2,1,1,3,0,1,4,1,0,65536,1,1,417,0,0,0,1,1,357,0,1,0,3,0,0]
theorem E95c7p0bound : E95c7p0.all wordBound = true := (by decide : [3047,17,7,112,99,49,35,49,48,50,0,17,0,0,36,4,1,1,439,0,1,1,295,0,1,3,2,1,1,3,0,1,4,1,0,65536,1,1,417,0,0,0,1,1,357,0,1,0,3,0,0].all wordBound = true)

def E95c7words : List Nat := E95c7p0

theorem E95c7wire : entryWords E95c7 = E95c7words := by
  rfl

theorem E95c7wordBound : E95c7words.all wordBound = true := by
  simp only [E95c7words,List.all_append,E95c7p0bound]
  try rfl

theorem E95c7bounded : ∀ n ∈ E95c7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c7wordBound

def E95c8 : Entry := ⟨3048, 17, [112,99,49,35,49,48,51], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 295 (0)) (.cons (.difference (.column 2 (0)) (.cons (.column 356 (0)) (.cons (.column 417 (0)) .nil))) .nil)))))⟩

def E95c8p0 : List Nat := [3048,17,7,112,99,49,35,49,48,51,0,17,0,0,24,4,1,1,439,0,1,1,295,0,1,3,1,2,0,1,1,356,0,1,1,417,0,0,0]
theorem E95c8p0bound : E95c8p0.all wordBound = true := (by decide : [3048,17,7,112,99,49,35,49,48,51,0,17,0,0,24,4,1,1,439,0,1,1,295,0,1,3,1,2,0,1,1,356,0,1,1,417,0,0,0].all wordBound = true)

def E95c8words : List Nat := E95c8p0

theorem E95c8wire : entryWords E95c8 = E95c8words := by
  rfl

theorem E95c8wordBound : E95c8words.all wordBound = true := by
  simp only [E95c8words,List.all_append,E95c8p0bound]
  try rfl

theorem E95c8bounded : ∀ n ∈ E95c8words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c8wordBound

def E95c9 : Entry := ⟨3049, 17, [112,99,49,35,49,48,52], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.sum (.cons (.product (.cons (.column 295 (0)) (.cons (.column 437 (0)) .nil))) (.cons (.product (.cons (.column 6 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))) .nil))) .nil))))⟩

def E95c9p0 : List Nat := [3049,17,7,112,99,49,35,49,48,52,0,17,0,0,36,4,1,1,439,0,1,2,1,4,1,1,295,0,1,1,437,0,0,1,4,1,1,6,0,1,3,0,1,1,1,295,0,0,0,0,0]
theorem E95c9p0bound : E95c9p0.all wordBound = true := (by decide : [3049,17,7,112,99,49,35,49,48,52,0,17,0,0,36,4,1,1,439,0,1,2,1,4,1,1,295,0,1,1,437,0,0,1,4,1,1,6,0,1,3,0,1,1,1,295,0,0,0,0,0].all wordBound = true)

def E95c9words : List Nat := E95c9p0

theorem E95c9wire : entryWords E95c9 = E95c9words := by
  rfl

theorem E95c9wordBound : E95c9words.all wordBound = true := by
  simp only [E95c9words,List.all_append,E95c9p0bound]
  try rfl

theorem E95c9bounded : ∀ n ∈ E95c9words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c9wordBound

def E95c10 : Entry := ⟨3050, 17, [112,99,49,35,49,48,53], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.difference (.sum (.cons (.column 6 (0)) (.cons (.constant ⟨2130706428, by decide⟩) (.cons (.product (.cons (.constant ⟨128, by decide⟩) (.cons (.column 297 (0)) .nil))) .nil)))) (.cons (.column 296 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil)))))⟩

def E95c10p0 : List Nat := [3050,17,7,112,99,49,35,49,48,53,0,17,0,0,41,4,1,1,439,0,1,3,2,1,1,6,0,1,0,2130706428,1,4,1,0,128,1,1,297,0,0,0,1,1,296,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c10p0bound : E95c10p0.all wordBound = true := (by decide : [3050,17,7,112,99,49,35,49,48,53,0,17,0,0,41,4,1,1,439,0,1,3,2,1,1,6,0,1,0,2130706428,1,4,1,0,128,1,1,297,0,0,0,1,1,296,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c10words : List Nat := E95c10p0

theorem E95c10wire : entryWords E95c10 = E95c10words := by
  rfl

theorem E95c10wordBound : E95c10words.all wordBound = true := by
  simp only [E95c10words,List.all_append,E95c10p0bound]
  try rfl

theorem E95c10bounded : ∀ n ∈ E95c10words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c10wordBound

def E95c11 : Entry := ⟨3051, 17, [112,99,49,35,49,48,54], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 217 (0)) (.cons (.column 6 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c11p0 : List Nat := [3051,17,7,112,99,49,35,49,48,54,0,17,0,0,29,4,1,1,439,0,1,1,297,0,1,3,1,217,0,1,1,6,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c11p0bound : E95c11p0.all wordBound = true := (by decide : [3051,17,7,112,99,49,35,49,48,54,0,17,0,0,29,4,1,1,439,0,1,1,297,0,1,3,1,217,0,1,1,6,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c11words : List Nat := E95c11p0

theorem E95c11wire : entryWords E95c11 = E95c11words := by
  rfl

theorem E95c11wordBound : E95c11words.all wordBound = true := by
  simp only [E95c11words,List.all_append,E95c11p0bound]
  try rfl

theorem E95c11bounded : ∀ n ∈ E95c11words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c11wordBound

def E95c12 : Entry := ⟨3052, 17, [112,99,49,35,49,48,55], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 226 (0)) (.cons (.column 6 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c12p0 : List Nat := [3052,17,7,112,99,49,35,49,48,55,0,17,0,0,29,4,1,1,439,0,1,1,297,0,1,3,1,226,0,1,1,6,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c12p0bound : E95c12p0.all wordBound = true := (by decide : [3052,17,7,112,99,49,35,49,48,55,0,17,0,0,29,4,1,1,439,0,1,1,297,0,1,3,1,226,0,1,1,6,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c12words : List Nat := E95c12p0

theorem E95c12wire : entryWords E95c12 = E95c12words := by
  rfl

theorem E95c12wordBound : E95c12words.all wordBound = true := by
  simp only [E95c12words,List.all_append,E95c12p0bound]
  try rfl

theorem E95c12bounded : ∀ n ∈ E95c12words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c12wordBound

def E95c13 : Entry := ⟨3053, 17, [112,99,49,35,49,48,56], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 235 (0)) (.cons (.constant ⟨88, by decide⟩) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c13p0 : List Nat := [3053,17,7,112,99,49,35,49,48,56,0,17,0,0,28,4,1,1,439,0,1,1,297,0,1,3,1,235,0,1,0,88,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c13p0bound : E95c13p0.all wordBound = true := (by decide : [3053,17,7,112,99,49,35,49,48,56,0,17,0,0,28,4,1,1,439,0,1,1,297,0,1,3,1,235,0,1,0,88,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c13words : List Nat := E95c13p0

theorem E95c13wire : entryWords E95c13 = E95c13words := by
  rfl

theorem E95c13wordBound : E95c13words.all wordBound = true := by
  simp only [E95c13words,List.all_append,E95c13p0bound]
  try rfl

theorem E95c13bounded : ∀ n ∈ E95c13words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c13wordBound

def E95c14 : Entry := ⟨3054, 17, [112,99,49,35,49,48,57], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.sum (.cons (.column 359 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 416 (0)) .nil))) .nil))) (.cons (.column 357 (0)) (.cons (.constant ⟨1, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c14p0 : List Nat := [3054,17,7,112,99,49,35,49,48,57,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,359,0,1,4,1,0,65536,1,1,416,0,0,0,1,1,357,0,1,0,1,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c14p0bound : E95c14p0.all wordBound = true := (by decide : [3054,17,7,112,99,49,35,49,48,57,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,359,0,1,4,1,0,65536,1,1,416,0,0,0,1,1,357,0,1,0,1,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c14words : List Nat := E95c14p0

theorem E95c14wire : entryWords E95c14 = E95c14words := by
  rfl

theorem E95c14wordBound : E95c14words.all wordBound = true := by
  simp only [E95c14words,List.all_append,E95c14p0bound]
  try rfl

theorem E95c14bounded : ∀ n ∈ E95c14words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c14wordBound

def E95c15 : Entry := ⟨3055, 17, [112,99,49,35,49,49,48], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 358 (0)) (.cons (.column 356 (0)) (.cons (.column 416 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c15p0 : List Nat := [3055,17,7,112,99,49,35,49,49,48,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,358,0,1,1,356,0,1,1,416,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c15p0bound : E95c15p0.all wordBound = true := (by decide : [3055,17,7,112,99,49,35,49,49,48,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,358,0,1,1,356,0,1,1,416,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c15words : List Nat := E95c15p0

theorem E95c15wire : entryWords E95c15 = E95c15words := by
  rfl

theorem E95c15wordBound : E95c15words.all wordBound = true := by
  simp only [E95c15words,List.all_append,E95c15p0bound]
  try rfl

theorem E95c15bounded : ∀ n ∈ E95c15words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c15wordBound

def E95c16 : Entry := ⟨3056, 17, [112,99,49,35,49,49,49], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.sum (.cons (.column 361 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 417 (0)) .nil))) .nil))) (.cons (.column 357 (0)) (.cons (.constant ⟨2, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c16p0 : List Nat := [3056,17,7,112,99,49,35,49,49,49,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,361,0,1,4,1,0,65536,1,1,417,0,0,0,1,1,357,0,1,0,2,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c16p0bound : E95c16p0.all wordBound = true := (by decide : [3056,17,7,112,99,49,35,49,49,49,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,361,0,1,4,1,0,65536,1,1,417,0,0,0,1,1,357,0,1,0,2,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c16words : List Nat := E95c16p0

theorem E95c16wire : entryWords E95c16 = E95c16words := by
  rfl

theorem E95c16wordBound : E95c16words.all wordBound = true := by
  simp only [E95c16words,List.all_append,E95c16p0bound]
  try rfl

theorem E95c16bounded : ∀ n ∈ E95c16words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c16wordBound

def E95c17 : Entry := ⟨3057, 17, [112,99,49,35,49,49,50], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 360 (0)) (.cons (.column 356 (0)) (.cons (.column 417 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c17p0 : List Nat := [3057,17,7,112,99,49,35,49,49,50,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,360,0,1,1,356,0,1,1,417,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c17p0bound : E95c17p0.all wordBound = true := (by decide : [3057,17,7,112,99,49,35,49,49,50,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,360,0,1,1,356,0,1,1,417,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c17words : List Nat := E95c17p0

theorem E95c17wire : entryWords E95c17 = E95c17words := by
  rfl

theorem E95c17wordBound : E95c17words.all wordBound = true := by
  simp only [E95c17words,List.all_append,E95c17p0bound]
  try rfl

theorem E95c17bounded : ∀ n ∈ E95c17words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c17wordBound

def E95c18 : Entry := ⟨3058, 17, [112,99,49,35,49,49,51], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 236 (0)) (.cons (.column 6 (0)) (.cons (.constant ⟨8, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c18p0 : List Nat := [3058,17,7,112,99,49,35,49,49,51,0,17,0,0,32,4,1,1,439,0,1,1,297,0,1,3,1,236,0,1,1,6,0,1,0,8,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c18p0bound : E95c18p0.all wordBound = true := (by decide : [3058,17,7,112,99,49,35,49,49,51,0,17,0,0,32,4,1,1,439,0,1,1,297,0,1,3,1,236,0,1,1,6,0,1,0,8,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c18words : List Nat := E95c18p0

theorem E95c18wire : entryWords E95c18 = E95c18words := by
  rfl

theorem E95c18wordBound : E95c18words.all wordBound = true := by
  simp only [E95c18words,List.all_append,E95c18p0bound]
  try rfl

theorem E95c18bounded : ∀ n ∈ E95c18words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c18wordBound

def E95c19 : Entry := ⟨3059, 17, [112,99,49,35,49,49,52], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 243 (0)) (.cons (.column 6 (0)) (.cons (.constant ⟨8, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c19p0 : List Nat := [3059,17,7,112,99,49,35,49,49,52,0,17,0,0,32,4,1,1,439,0,1,1,297,0,1,3,1,243,0,1,1,6,0,1,0,8,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c19p0bound : E95c19p0.all wordBound = true := (by decide : [3059,17,7,112,99,49,35,49,49,52,0,17,0,0,32,4,1,1,439,0,1,1,297,0,1,3,1,243,0,1,1,6,0,1,0,8,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c19words : List Nat := E95c19p0

theorem E95c19wire : entryWords E95c19 = E95c19words := by
  rfl

theorem E95c19wordBound : E95c19words.all wordBound = true := by
  simp only [E95c19words,List.all_append,E95c19p0bound]
  try rfl

theorem E95c19bounded : ∀ n ∈ E95c19words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c19wordBound

def E95c20 : Entry := ⟨3060, 17, [112,99,49,35,49,49,53], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.sum (.cons (.column 363 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 418 (0)) .nil))) .nil))) (.cons (.column 357 (0)) (.cons (.constant ⟨3, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c20p0 : List Nat := [3060,17,7,112,99,49,35,49,49,53,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,363,0,1,4,1,0,65536,1,1,418,0,0,0,1,1,357,0,1,0,3,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c20p0bound : E95c20p0.all wordBound = true := (by decide : [3060,17,7,112,99,49,35,49,49,53,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,363,0,1,4,1,0,65536,1,1,418,0,0,0,1,1,357,0,1,0,3,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c20words : List Nat := E95c20p0

theorem E95c20wire : entryWords E95c20 = E95c20words := by
  rfl

theorem E95c20wordBound : E95c20words.all wordBound = true := by
  simp only [E95c20words,List.all_append,E95c20p0bound]
  try rfl

theorem E95c20bounded : ∀ n ∈ E95c20words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c20wordBound

def E95c21 : Entry := ⟨3061, 17, [112,99,49,35,49,49,54], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 362 (0)) (.cons (.column 356 (0)) (.cons (.column 418 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c21p0 : List Nat := [3061,17,7,112,99,49,35,49,49,54,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,362,0,1,1,356,0,1,1,418,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c21p0bound : E95c21p0.all wordBound = true := (by decide : [3061,17,7,112,99,49,35,49,49,54,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,362,0,1,1,356,0,1,1,418,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c21words : List Nat := E95c21p0

theorem E95c21wire : entryWords E95c21 = E95c21words := by
  rfl

theorem E95c21wordBound : E95c21words.all wordBound = true := by
  simp only [E95c21words,List.all_append,E95c21p0bound]
  try rfl

theorem E95c21bounded : ∀ n ∈ E95c21words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c21wordBound

def E95c22 : Entry := ⟨3062, 17, [112,99,49,35,49,49,55], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 248 (0)) (.cons (.constant ⟨89, by decide⟩) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c22p0 : List Nat := [3062,17,7,112,99,49,35,49,49,55,0,17,0,0,28,4,1,1,439,0,1,1,297,0,1,3,1,248,0,1,0,89,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c22p0bound : E95c22p0.all wordBound = true := (by decide : [3062,17,7,112,99,49,35,49,49,55,0,17,0,0,28,4,1,1,439,0,1,1,297,0,1,3,1,248,0,1,0,89,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c22words : List Nat := E95c22p0

theorem E95c22wire : entryWords E95c22 = E95c22words := by
  rfl

theorem E95c22wordBound : E95c22words.all wordBound = true := by
  simp only [E95c22words,List.all_append,E95c22p0bound]
  try rfl

theorem E95c22bounded : ∀ n ∈ E95c22words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c22wordBound

def E95c23 : Entry := ⟨3063, 17, [112,99,49,35,49,49,56], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.sum (.cons (.column 365 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 419 (0)) .nil))) .nil))) (.cons (.column 357 (0)) (.cons (.constant ⟨4, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c23p0 : List Nat := [3063,17,7,112,99,49,35,49,49,56,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,365,0,1,4,1,0,65536,1,1,419,0,0,0,1,1,357,0,1,0,4,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c23p0bound : E95c23p0.all wordBound = true := (by decide : [3063,17,7,112,99,49,35,49,49,56,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,365,0,1,4,1,0,65536,1,1,419,0,0,0,1,1,357,0,1,0,4,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c23words : List Nat := E95c23p0

theorem E95c23wire : entryWords E95c23 = E95c23words := by
  rfl

theorem E95c23wordBound : E95c23words.all wordBound = true := by
  simp only [E95c23words,List.all_append,E95c23p0bound]
  try rfl

theorem E95c23bounded : ∀ n ∈ E95c23words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c23wordBound

def E95c24 : Entry := ⟨3064, 17, [112,99,49,35,49,49,57], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 364 (0)) (.cons (.column 356 (0)) (.cons (.column 419 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c24p0 : List Nat := [3064,17,7,112,99,49,35,49,49,57,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,364,0,1,1,356,0,1,1,419,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c24p0bound : E95c24p0.all wordBound = true := (by decide : [3064,17,7,112,99,49,35,49,49,57,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,364,0,1,1,356,0,1,1,419,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c24words : List Nat := E95c24p0

theorem E95c24wire : entryWords E95c24 = E95c24words := by
  rfl

theorem E95c24wordBound : E95c24words.all wordBound = true := by
  simp only [E95c24words,List.all_append,E95c24p0bound]
  try rfl

theorem E95c24bounded : ∀ n ∈ E95c24words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c24wordBound

def E95c25 : Entry := ⟨3065, 17, [112,99,49,35,49,50,48], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.sum (.cons (.column 367 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 420 (0)) .nil))) .nil))) (.cons (.column 357 (0)) (.cons (.constant ⟨5, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c25p0 : List Nat := [3065,17,7,112,99,49,35,49,50,48,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,367,0,1,4,1,0,65536,1,1,420,0,0,0,1,1,357,0,1,0,5,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c25p0bound : E95c25p0.all wordBound = true := (by decide : [3065,17,7,112,99,49,35,49,50,48,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,367,0,1,4,1,0,65536,1,1,420,0,0,0,1,1,357,0,1,0,5,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c25words : List Nat := E95c25p0

theorem E95c25wire : entryWords E95c25 = E95c25words := by
  rfl

theorem E95c25wordBound : E95c25words.all wordBound = true := by
  simp only [E95c25words,List.all_append,E95c25p0bound]
  try rfl

theorem E95c25bounded : ∀ n ∈ E95c25words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c25wordBound

def E95c26 : Entry := ⟨3066, 17, [112,99,49,35,49,50,49], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 366 (0)) (.cons (.column 356 (0)) (.cons (.column 420 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c26p0 : List Nat := [3066,17,7,112,99,49,35,49,50,49,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,366,0,1,1,356,0,1,1,420,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c26p0bound : E95c26p0.all wordBound = true := (by decide : [3066,17,7,112,99,49,35,49,50,49,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,366,0,1,1,356,0,1,1,420,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c26words : List Nat := E95c26p0

theorem E95c26wire : entryWords E95c26 = E95c26words := by
  rfl

theorem E95c26wordBound : E95c26words.all wordBound = true := by
  simp only [E95c26words,List.all_append,E95c26p0bound]
  try rfl

theorem E95c26bounded : ∀ n ∈ E95c26words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c26wordBound

def E95c27 : Entry := ⟨3067, 17, [112,99,49,35,49,50,50], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 249 (0)) (.cons (.column 6 (0)) (.cons (.constant ⟨16, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c27p0 : List Nat := [3067,17,7,112,99,49,35,49,50,50,0,17,0,0,32,4,1,1,439,0,1,1,297,0,1,3,1,249,0,1,1,6,0,1,0,16,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c27p0bound : E95c27p0.all wordBound = true := (by decide : [3067,17,7,112,99,49,35,49,50,50,0,17,0,0,32,4,1,1,439,0,1,1,297,0,1,3,1,249,0,1,1,6,0,1,0,16,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c27words : List Nat := E95c27p0

theorem E95c27wire : entryWords E95c27 = E95c27words := by
  rfl

theorem E95c27wordBound : E95c27words.all wordBound = true := by
  simp only [E95c27words,List.all_append,E95c27p0bound]
  try rfl

theorem E95c27bounded : ∀ n ∈ E95c27words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c27wordBound

def E95c28 : Entry := ⟨3068, 17, [112,99,49,35,49,50,51], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 258 (0)) (.cons (.column 6 (0)) (.cons (.constant ⟨16, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c28p0 : List Nat := [3068,17,7,112,99,49,35,49,50,51,0,17,0,0,32,4,1,1,439,0,1,1,297,0,1,3,1,258,0,1,1,6,0,1,0,16,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c28p0bound : E95c28p0.all wordBound = true := (by decide : [3068,17,7,112,99,49,35,49,50,51,0,17,0,0,32,4,1,1,439,0,1,1,297,0,1,3,1,258,0,1,1,6,0,1,0,16,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c28words : List Nat := E95c28p0

theorem E95c28wire : entryWords E95c28 = E95c28words := by
  rfl

theorem E95c28wordBound : E95c28words.all wordBound = true := by
  simp only [E95c28words,List.all_append,E95c28p0bound]
  try rfl

theorem E95c28bounded : ∀ n ∈ E95c28words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c28wordBound

def E95c29 : Entry := ⟨3069, 17, [112,99,49,35,49,50,52], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.sum (.cons (.column 369 (0)) (.cons (.product (.cons (.constant ⟨65536, by decide⟩) (.cons (.column 421 (0)) .nil))) .nil))) (.cons (.column 357 (0)) (.cons (.constant ⟨6, by decide⟩) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c29p0 : List Nat := [3069,17,7,112,99,49,35,49,50,52,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,369,0,1,4,1,0,65536,1,1,421,0,0,0,1,1,357,0,1,0,6,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c29p0bound : E95c29p0.all wordBound = true := (by decide : [3069,17,7,112,99,49,35,49,50,52,0,17,0,0,45,4,1,1,439,0,1,1,297,0,1,3,2,1,1,369,0,1,4,1,0,65536,1,1,421,0,0,0,1,1,357,0,1,0,6,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c29words : List Nat := E95c29p0

theorem E95c29wire : entryWords E95c29 = E95c29words := by
  rfl

theorem E95c29wordBound : E95c29words.all wordBound = true := by
  simp only [E95c29words,List.all_append,E95c29p0bound]
  try rfl

theorem E95c29bounded : ∀ n ∈ E95c29words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c29wordBound

def E95c30 : Entry := ⟨3070, 17, [112,99,49,35,49,50,53], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 368 (0)) (.cons (.column 356 (0)) (.cons (.column 421 (0)) .nil))) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c30p0 : List Nat := [3070,17,7,112,99,49,35,49,50,53,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,368,0,1,1,356,0,1,1,421,0,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c30p0bound : E95c30p0.all wordBound = true := (by decide : [3070,17,7,112,99,49,35,49,50,53,0,17,0,0,33,4,1,1,439,0,1,1,297,0,1,3,1,368,0,1,1,356,0,1,1,421,0,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c30words : List Nat := E95c30p0

theorem E95c30wire : entryWords E95c30 = E95c30words := by
  rfl

theorem E95c30wordBound : E95c30words.all wordBound = true := by
  simp only [E95c30words,List.all_append,E95c30p0bound]
  try rfl

theorem E95c30bounded : ∀ n ∈ E95c30words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c30wordBound

def E95c31 : Entry := ⟨3071, 17, [112,99,49,35,49,50,54], (.vanishing 17 none (.product (.cons (.column 439 (0)) (.cons (.column 297 (0)) (.cons (.difference (.column 263 (0)) (.cons (.constant ⟨90, by decide⟩) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 295 (0)) .nil)) .nil))))))⟩

def E95c31p0 : List Nat := [3071,17,7,112,99,49,35,49,50,54,0,17,0,0,28,4,1,1,439,0,1,1,297,0,1,3,1,263,0,1,0,90,0,1,3,0,1,1,1,295,0,0,0]
theorem E95c31p0bound : E95c31p0.all wordBound = true := (by decide : [3071,17,7,112,99,49,35,49,50,54,0,17,0,0,28,4,1,1,439,0,1,1,297,0,1,3,1,263,0,1,0,90,0,1,3,0,1,1,1,295,0,0,0].all wordBound = true)

def E95c31words : List Nat := E95c31p0

theorem E95c31wire : entryWords E95c31 = E95c31words := by
  rfl

theorem E95c31wordBound : E95c31words.all wordBound = true := by
  simp only [E95c31words,List.all_append,E95c31p0bound]
  try rfl

theorem E95c31bounded : ∀ n ∈ E95c31words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E95c31wordBound

def E95 : List Entry := [E95c0,E95c1,E95c2,E95c3,E95c4,E95c5,E95c6,E95c7,E95c8,E95c9,E95c10,E95c11,E95c12,E95c13,E95c14,E95c15,E95c16,E95c17,E95c18,E95c19,E95c20,E95c21,E95c22,E95c23,E95c24,E95c25,E95c26,E95c27,E95c28,E95c29,E95c30,E95c31]

def E95words : List Nat := E95c0words ++ E95c1words ++ E95c2words ++ E95c3words ++ E95c4words ++ E95c5words ++ E95c6words ++ E95c7words ++ E95c8words ++ E95c9words ++ E95c10words ++ E95c11words ++ E95c12words ++ E95c13words ++ E95c14words ++ E95c15words ++ E95c16words ++ E95c17words ++ E95c18words ++ E95c19words ++ E95c20words ++ E95c21words ++ E95c22words ++ E95c23words ++ E95c24words ++ E95c25words ++ E95c26words ++ E95c27words ++ E95c28words ++ E95c29words ++ E95c30words ++ E95c31words

theorem E95wire : E95.flatMap entry.encode = E95words := by
  rw [entry_fast_fun]
  simp only [E95,List.flatMap_cons,List.flatMap_nil,List.append_nil,E95c0wire,E95c1wire,E95c2wire,E95c3wire,E95c4wire,E95c5wire,E95c6wire,E95c7wire,E95c8wire,E95c9wire,E95c10wire,E95c11wire,E95c12wire,E95c13wire,E95c14wire,E95c15wire,E95c16wire,E95c17wire,E95c18wire,E95c19wire,E95c20wire,E95c21wire,E95c22wire,E95c23wire,E95c24wire,E95c25wire,E95c26wire,E95c27wire,E95c28wire,E95c29wire,E95c30wire,E95c31wire]
  rfl

theorem E95wordBound : E95words.all wordBound = true := by
  simp only [E95words,List.all_append,E95c0wordBound,E95c1wordBound,E95c2wordBound,E95c3wordBound,E95c4wordBound,E95c5wordBound,E95c6wordBound,E95c7wordBound,E95c8wordBound,E95c9wordBound,E95c10wordBound,E95c11wordBound,E95c12wordBound,E95c13wordBound,E95c14wordBound,E95c15wordBound,E95c16wordBound,E95c17wordBound,E95c18wordBound,E95c19wordBound,E95c20wordBound,E95c21wordBound,E95c22wordBound,E95c23wordBound,E95c24wordBound,E95c25wordBound,E95c26wordBound,E95c27wordBound,E95c28wordBound,E95c29wordBound,E95c30wordBound,E95c31wordBound]
  decide

theorem E95bounded : ∀ n ∈ E95words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using E95wordBound

theorem E95length : E95.length = 32 := by rfl

def E95selected : List RawConstraint := []
theorem E95select : (E95.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).map Entry.rule = E95selected := by rfl

def E95incoming : List RawConstraint := []
theorem E95calls : (ArtifactBinding.incomingEntries ⟨[],E95⟩).map Entry.rule = E95incoming := by rfl

theorem E95closure : (E95.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).all (fun e => (ArtifactBinding.referencedModules e).all (fun id => decide (id ∈ ArtifactBinding.selectedIds))) = true := by decide

end DivRemFV.Replay
