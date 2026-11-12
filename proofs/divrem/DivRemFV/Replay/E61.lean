import DivRemFV.ReplaySupport

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace DivRemFV.Replay
open NativeImport ArtifactWire

def E61c0 : Entry := ⟨1952, 12, [114,97,109,95,49,50,95,48,95,56,51,95,57], (.lookup [⟨12, (some (152)), #[44,28,29,30,31,3,4]⟩] [⟨9, (some (18)), #[0,1,2,3,4,11,12]⟩])⟩

def E61c0p0 : List Nat := [1952,12,13,114,97,109,95,49,50,95,48,95,56,51,95,57,1,1,0,1,12,1,152,7,44,28,29,30,31,3,4,1,9,1,18,7,0,1,2,3,4,11,12]
theorem E61c0p0bound : E61c0p0.all wordBound = true := (by decide : [1952,12,13,114,97,109,95,49,50,95,48,95,56,51,95,57,1,1,0,1,12,1,152,7,44,28,29,30,31,3,4,1,9,1,18,7,0,1,2,3,4,11,12].all wordBound = true)

def E61c0words : List Nat := E61c0p0

theorem E61c0wire : entryWords E61c0 = E61c0words := by
  rfl

theorem E61c0wordBound : E61c0words.all wordBound = true := by
  simp only [E61c0words,List.all_append,E61c0p0bound]
  try rfl

theorem E61c0bounded : ∀ n ∈ E61c0words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c0wordBound

def E61c1 : Entry := ⟨1953, 12, [108,111,111,107,117,112,95,115,101,108,95,49,53,51,35,48], (.vanishing 12 none (.sum (.cons (.product (.cons (.column 55 (0)) (.cons (.column 144 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 153 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 55 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 144 (0)) .nil)) .nil))) (.cons (.column 153 (0)) .nil))) .nil))))⟩

def E61c1p0 : List Nat := [1953,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,51,35,48,0,12,0,0,50,2,1,4,1,1,55,0,1,1,144,0,1,3,0,1,1,1,153,0,0,0,1,4,1,2,1,3,0,1,1,1,55,0,0,1,3,0,1,1,1,144,0,0,0,1,1,153,0,0,0]
theorem E61c1p0bound : E61c1p0.all wordBound = true := (by decide : [1953,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,51,35,48,0,12,0,0,50,2,1,4,1,1,55,0,1,1,144,0,1,3,0,1,1,1,153,0,0,0,1,4,1,2,1,3,0,1,1,1,55,0,0,1,3,0,1,1,1,144,0,0,0,1,1,153,0,0,0].all wordBound = true)

def E61c1words : List Nat := E61c1p0

theorem E61c1wire : entryWords E61c1 = E61c1words := by
  rfl

theorem E61c1wordBound : E61c1words.all wordBound = true := by
  simp only [E61c1words,List.all_append,E61c1p0bound]
  try rfl

theorem E61c1bounded : ∀ n ∈ E61c1words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c1wordBound

def E61c2 : Entry := ⟨1954, 12, [99,97,108,108,95,49,50,95,49,95,53,48], (.lookup [⟨12, (some (153)), #[86,87,88,32,33,34,35,40,41,42,28,29,30,31]⟩] [⟨50, (some (45)), #[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩])⟩

def E61c2p0 : List Nat := [1954,12,12,99,97,108,108,95,49,50,95,49,95,53,48,1,1,0,1,12,1,153,14,86,87,88,32,33,34,35,40,41,42,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem E61c2p0bound : E61c2p0.all wordBound = true := (by decide : [1954,12,12,99,97,108,108,95,49,50,95,49,95,53,48,1,1,0,1,12,1,153,14,86,87,88,32,33,34,35,40,41,42,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13].all wordBound = true)

def E61c2words : List Nat := E61c2p0

theorem E61c2wire : entryWords E61c2 = E61c2words := by
  rfl

theorem E61c2wordBound : E61c2words.all wordBound = true := by
  simp only [E61c2words,List.all_append,E61c2p0bound]
  try rfl

theorem E61c2bounded : ∀ n ∈ E61c2words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c2wordBound

def E61c3 : Entry := ⟨1955, 12, [114,97,109,95,49,50,95,49,95,50,53,95,57], (.lookup [⟨12, (some (153)), #[27,28,29,30,31,89,90]⟩] [⟨9, (some (18)), #[0,1,2,3,4,11,12]⟩])⟩

def E61c3p0 : List Nat := [1955,12,13,114,97,109,95,49,50,95,49,95,50,53,95,57,1,1,0,1,12,1,153,7,27,28,29,30,31,89,90,1,9,1,18,7,0,1,2,3,4,11,12]
theorem E61c3p0bound : E61c3p0.all wordBound = true := (by decide : [1955,12,13,114,97,109,95,49,50,95,49,95,50,53,95,57,1,1,0,1,12,1,153,7,27,28,29,30,31,89,90,1,9,1,18,7,0,1,2,3,4,11,12].all wordBound = true)

def E61c3words : List Nat := E61c3p0

theorem E61c3wire : entryWords E61c3 = E61c3words := by
  rfl

theorem E61c3wordBound : E61c3words.all wordBound = true := by
  simp only [E61c3words,List.all_append,E61c3p0bound]
  try rfl

theorem E61c3bounded : ∀ n ∈ E61c3words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c3wordBound

def E61c4 : Entry := ⟨1956, 12, [108,111,111,107,117,112,95,115,101,108,95,49,53,52,35,48], (.vanishing 12 none (.sum (.cons (.product (.cons (.column 144 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 154 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 55 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.column 55 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 144 (0)) .nil)) .nil))) (.cons (.column 154 (0)) .nil))) .nil))))⟩

def E61c4p0 : List Nat := [1956,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,52,35,48,0,12,0,0,50,2,1,4,1,1,144,0,1,3,0,1,1,1,154,0,0,1,3,0,1,1,1,55,0,0,0,1,4,1,2,1,1,55,0,1,3,0,1,1,1,144,0,0,0,1,1,154,0,0,0]
theorem E61c4p0bound : E61c4p0.all wordBound = true := (by decide : [1956,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,52,35,48,0,12,0,0,50,2,1,4,1,1,144,0,1,3,0,1,1,1,154,0,0,1,3,0,1,1,1,55,0,0,0,1,4,1,2,1,1,55,0,1,3,0,1,1,1,144,0,0,0,1,1,154,0,0,0].all wordBound = true)

def E61c4words : List Nat := E61c4p0

theorem E61c4wire : entryWords E61c4 = E61c4words := by
  rfl

theorem E61c4wordBound : E61c4words.all wordBound = true := by
  simp only [E61c4words,List.all_append,E61c4p0bound]
  try rfl

theorem E61c4bounded : ∀ n ∈ E61c4words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c4wordBound

def E61c5 : Entry := ⟨1957, 12, [99,97,108,108,95,49,50,95,49,95,49,51], (.lookup [⟨12, (some (154)), #[91,92,58,59]⟩] [⟨13, (some (410)), #[0,1,2,3]⟩])⟩

def E61c5p0 : List Nat := [1957,12,12,99,97,108,108,95,49,50,95,49,95,49,51,1,1,0,1,12,1,154,4,91,92,58,59,1,13,1,410,4,0,1,2,3]
theorem E61c5p0bound : E61c5p0.all wordBound = true := (by decide : [1957,12,12,99,97,108,108,95,49,50,95,49,95,49,51,1,1,0,1,12,1,154,4,91,92,58,59,1,13,1,410,4,0,1,2,3].all wordBound = true)

def E61c5words : List Nat := E61c5p0

theorem E61c5wire : entryWords E61c5 = E61c5words := by
  rfl

theorem E61c5wordBound : E61c5words.all wordBound = true := by
  simp only [E61c5words,List.all_append,E61c5p0bound]
  try rfl

theorem E61c5bounded : ∀ n ∈ E61c5words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c5wordBound

def E61c6 : Entry := ⟨1958, 12, [99,97,108,108,95,49,50,95,49,95,49,53], (.lookup [⟨12, (some (154)), #[58,59,60,61]⟩] [⟨15, (some (15)), #[0,1,2,3]⟩])⟩

def E61c6p0 : List Nat := [1958,12,12,99,97,108,108,95,49,50,95,49,95,49,53,1,1,0,1,12,1,154,4,58,59,60,61,1,15,1,15,4,0,1,2,3]
theorem E61c6p0bound : E61c6p0.all wordBound = true := (by decide : [1958,12,12,99,97,108,108,95,49,50,95,49,95,49,53,1,1,0,1,12,1,154,4,58,59,60,61,1,15,1,15,4,0,1,2,3].all wordBound = true)

def E61c6words : List Nat := E61c6p0

theorem E61c6wire : entryWords E61c6 = E61c6words := by
  rfl

theorem E61c6wordBound : E61c6words.all wordBound = true := by
  simp only [E61c6words,List.all_append,E61c6p0bound]
  try rfl

theorem E61c6bounded : ∀ n ∈ E61c6words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c6wordBound

def E61c7 : Entry := ⟨1959, 12, [108,111,111,107,117,112,95,115,101,108,95,49,53,53,35,48], (.vanishing 12 none (.product (.cons (.column 57 (0)) (.cons (.column 144 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 155 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.product (.cons (.sum (.cons (.column 53 (0)) (.cons (.column 55 (0)) .nil))) (.cons (.column 175 (0)) .nil))) .nil)) .nil))))))⟩

def E61c7p0 : List Nat := [1959,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,53,35,48,0,12,0,0,42,4,1,1,57,0,1,1,144,0,1,3,0,1,1,1,155,0,0,1,3,0,1,1,4,1,2,1,1,53,0,1,1,55,0,0,1,1,175,0,0,0,0]
theorem E61c7p0bound : E61c7p0.all wordBound = true := (by decide : [1959,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,53,35,48,0,12,0,0,42,4,1,1,57,0,1,1,144,0,1,3,0,1,1,1,155,0,0,1,3,0,1,1,4,1,2,1,1,53,0,1,1,55,0,0,1,1,175,0,0,0,0].all wordBound = true)

def E61c7words : List Nat := E61c7p0

theorem E61c7wire : entryWords E61c7 = E61c7words := by
  rfl

theorem E61c7wordBound : E61c7words.all wordBound = true := by
  simp only [E61c7words,List.all_append,E61c7p0bound]
  try rfl

theorem E61c7bounded : ∀ n ∈ E61c7words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c7wordBound

def E61c8 : Entry := ⟨1960, 12, [108,111,111,107,117,112,95,115,101,108,95,49,53,53,35,49], (.vanishing 12 none (.product (.cons (.sum (.cons (.column 53 (0)) (.cons (.column 55 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 57 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 144 (0)) .nil)) .nil))))) (.cons (.column 155 (0)) .nil))))⟩

def E61c8p0 : List Nat := [1960,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,53,35,49,0,12,0,0,35,4,1,2,1,1,53,0,1,1,55,0,1,3,0,1,1,1,57,0,0,1,3,0,1,1,1,144,0,0,0,1,1,155,0,0]
theorem E61c8p0bound : E61c8p0.all wordBound = true := (by decide : [1960,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,53,35,49,0,12,0,0,35,4,1,2,1,1,53,0,1,1,55,0,1,3,0,1,1,1,57,0,0,1,3,0,1,1,1,144,0,0,0,1,1,155,0,0].all wordBound = true)

def E61c8words : List Nat := E61c8p0

theorem E61c8wire : entryWords E61c8 = E61c8words := by
  rfl

theorem E61c8wordBound : E61c8words.all wordBound = true := by
  simp only [E61c8words,List.all_append,E61c8p0bound]
  try rfl

theorem E61c8bounded : ∀ n ∈ E61c8words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c8wordBound

def E61c9 : Entry := ⟨1961, 12, [99,97,108,108,95,49,50,95,49,95,53,48], (.lookup [⟨12, (some (155)), #[93,94,95,32,33,34,35,62,63,64,28,29,30,31]⟩] [⟨50, (some (45)), #[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩])⟩

def E61c9p0 : List Nat := [1961,12,12,99,97,108,108,95,49,50,95,49,95,53,48,1,1,0,1,12,1,155,14,93,94,95,32,33,34,35,62,63,64,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem E61c9p0bound : E61c9p0.all wordBound = true := (by decide : [1961,12,12,99,97,108,108,95,49,50,95,49,95,53,48,1,1,0,1,12,1,155,14,93,94,95,32,33,34,35,62,63,64,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13].all wordBound = true)

def E61c9words : List Nat := E61c9p0

theorem E61c9wire : entryWords E61c9 = E61c9words := by
  rfl

theorem E61c9wordBound : E61c9words.all wordBound = true := by
  simp only [E61c9words,List.all_append,E61c9p0bound]
  try rfl

theorem E61c9bounded : ∀ n ∈ E61c9words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c9wordBound

def E61c10 : Entry := ⟨1962, 12, [114,97,109,95,49,50,95,49,95,57,54,95,57], (.lookup [⟨12, (some (155)), #[44,28,29,30,31,60,61]⟩] [⟨9, (some (18)), #[0,1,2,3,4,11,12]⟩])⟩

def E61c10p0 : List Nat := [1962,12,13,114,97,109,95,49,50,95,49,95,57,54,95,57,1,1,0,1,12,1,155,7,44,28,29,30,31,60,61,1,9,1,18,7,0,1,2,3,4,11,12]
theorem E61c10p0bound : E61c10p0.all wordBound = true := (by decide : [1962,12,13,114,97,109,95,49,50,95,49,95,57,54,95,57,1,1,0,1,12,1,155,7,44,28,29,30,31,60,61,1,9,1,18,7,0,1,2,3,4,11,12].all wordBound = true)

def E61c10words : List Nat := E61c10p0

theorem E61c10wire : entryWords E61c10 = E61c10words := by
  rfl

theorem E61c10wordBound : E61c10words.all wordBound = true := by
  simp only [E61c10words,List.all_append,E61c10p0bound]
  try rfl

theorem E61c10bounded : ∀ n ∈ E61c10words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c10wordBound

def E61c11 : Entry := ⟨1963, 12, [108,111,111,107,117,112,95,115,101,108,95,49,53,54,35,48], (.vanishing 12 none (.sum (.cons (.product (.cons (.column 55 (0)) (.cons (.column 145 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 156 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 55 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 145 (0)) .nil)) .nil))) (.cons (.column 156 (0)) .nil))) .nil))))⟩

def E61c11p0 : List Nat := [1963,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,54,35,48,0,12,0,0,50,2,1,4,1,1,55,0,1,1,145,0,1,3,0,1,1,1,156,0,0,0,1,4,1,2,1,3,0,1,1,1,55,0,0,1,3,0,1,1,1,145,0,0,0,1,1,156,0,0,0]
theorem E61c11p0bound : E61c11p0.all wordBound = true := (by decide : [1963,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,54,35,48,0,12,0,0,50,2,1,4,1,1,55,0,1,1,145,0,1,3,0,1,1,1,156,0,0,0,1,4,1,2,1,3,0,1,1,1,55,0,0,1,3,0,1,1,1,145,0,0,0,1,1,156,0,0,0].all wordBound = true)

def E61c11words : List Nat := E61c11p0

theorem E61c11wire : entryWords E61c11 = E61c11words := by
  rfl

theorem E61c11wordBound : E61c11words.all wordBound = true := by
  simp only [E61c11words,List.all_append,E61c11p0bound]
  try rfl

theorem E61c11bounded : ∀ n ∈ E61c11words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c11wordBound

def E61c12 : Entry := ⟨1964, 12, [99,97,108,108,95,49,50,95,50,95,53,48], (.lookup [⟨12, (some (156)), #[96,97,98,32,33,34,35,40,41,42,28,29,30,31]⟩] [⟨50, (some (45)), #[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩])⟩

def E61c12p0 : List Nat := [1964,12,12,99,97,108,108,95,49,50,95,50,95,53,48,1,1,0,1,12,1,156,14,96,97,98,32,33,34,35,40,41,42,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem E61c12p0bound : E61c12p0.all wordBound = true := (by decide : [1964,12,12,99,97,108,108,95,49,50,95,50,95,53,48,1,1,0,1,12,1,156,14,96,97,98,32,33,34,35,40,41,42,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13].all wordBound = true)

def E61c12words : List Nat := E61c12p0

theorem E61c12wire : entryWords E61c12 = E61c12words := by
  rfl

theorem E61c12wordBound : E61c12words.all wordBound = true := by
  simp only [E61c12words,List.all_append,E61c12p0bound]
  try rfl

theorem E61c12bounded : ∀ n ∈ E61c12words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c12wordBound

def E61c13 : Entry := ⟨1965, 12, [114,97,109,95,49,50,95,50,95,50,54,95,57], (.lookup [⟨12, (some (156)), #[27,28,29,30,31,99,100]⟩] [⟨9, (some (18)), #[0,1,2,3,4,11,12]⟩])⟩

def E61c13p0 : List Nat := [1965,12,13,114,97,109,95,49,50,95,50,95,50,54,95,57,1,1,0,1,12,1,156,7,27,28,29,30,31,99,100,1,9,1,18,7,0,1,2,3,4,11,12]
theorem E61c13p0bound : E61c13p0.all wordBound = true := (by decide : [1965,12,13,114,97,109,95,49,50,95,50,95,50,54,95,57,1,1,0,1,12,1,156,7,27,28,29,30,31,99,100,1,9,1,18,7,0,1,2,3,4,11,12].all wordBound = true)

def E61c13words : List Nat := E61c13p0

theorem E61c13wire : entryWords E61c13 = E61c13words := by
  rfl

theorem E61c13wordBound : E61c13words.all wordBound = true := by
  simp only [E61c13words,List.all_append,E61c13p0bound]
  try rfl

theorem E61c13bounded : ∀ n ∈ E61c13words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c13wordBound

def E61c14 : Entry := ⟨1966, 12, [108,111,111,107,117,112,95,115,101,108,95,49,53,55,35,48], (.vanishing 12 none (.sum (.cons (.product (.cons (.column 145 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 157 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 55 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.column 55 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 145 (0)) .nil)) .nil))) (.cons (.column 157 (0)) .nil))) .nil))))⟩

def E61c14p0 : List Nat := [1966,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,55,35,48,0,12,0,0,50,2,1,4,1,1,145,0,1,3,0,1,1,1,157,0,0,1,3,0,1,1,1,55,0,0,0,1,4,1,2,1,1,55,0,1,3,0,1,1,1,145,0,0,0,1,1,157,0,0,0]
theorem E61c14p0bound : E61c14p0.all wordBound = true := (by decide : [1966,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,55,35,48,0,12,0,0,50,2,1,4,1,1,145,0,1,3,0,1,1,1,157,0,0,1,3,0,1,1,1,55,0,0,0,1,4,1,2,1,1,55,0,1,3,0,1,1,1,145,0,0,0,1,1,157,0,0,0].all wordBound = true)

def E61c14words : List Nat := E61c14p0

theorem E61c14wire : entryWords E61c14 = E61c14words := by
  rfl

theorem E61c14wordBound : E61c14words.all wordBound = true := by
  simp only [E61c14words,List.all_append,E61c14p0bound]
  try rfl

theorem E61c14bounded : ∀ n ∈ E61c14words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c14wordBound

def E61c15 : Entry := ⟨1967, 12, [99,97,108,108,95,49,50,95,50,95,49,51], (.lookup [⟨12, (some (157)), #[101,102,58,59]⟩] [⟨13, (some (410)), #[0,1,2,3]⟩])⟩

def E61c15p0 : List Nat := [1967,12,12,99,97,108,108,95,49,50,95,50,95,49,51,1,1,0,1,12,1,157,4,101,102,58,59,1,13,1,410,4,0,1,2,3]
theorem E61c15p0bound : E61c15p0.all wordBound = true := (by decide : [1967,12,12,99,97,108,108,95,49,50,95,50,95,49,51,1,1,0,1,12,1,157,4,101,102,58,59,1,13,1,410,4,0,1,2,3].all wordBound = true)

def E61c15words : List Nat := E61c15p0

theorem E61c15wire : entryWords E61c15 = E61c15words := by
  rfl

theorem E61c15wordBound : E61c15words.all wordBound = true := by
  simp only [E61c15words,List.all_append,E61c15p0bound]
  try rfl

theorem E61c15bounded : ∀ n ∈ E61c15words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c15wordBound

def E61c16 : Entry := ⟨1968, 12, [99,97,108,108,95,49,50,95,50,95,49,53], (.lookup [⟨12, (some (157)), #[58,59,60,61]⟩] [⟨15, (some (15)), #[0,1,2,3]⟩])⟩

def E61c16p0 : List Nat := [1968,12,12,99,97,108,108,95,49,50,95,50,95,49,53,1,1,0,1,12,1,157,4,58,59,60,61,1,15,1,15,4,0,1,2,3]
theorem E61c16p0bound : E61c16p0.all wordBound = true := (by decide : [1968,12,12,99,97,108,108,95,49,50,95,50,95,49,53,1,1,0,1,12,1,157,4,58,59,60,61,1,15,1,15,4,0,1,2,3].all wordBound = true)

def E61c16words : List Nat := E61c16p0

theorem E61c16wire : entryWords E61c16 = E61c16words := by
  rfl

theorem E61c16wordBound : E61c16words.all wordBound = true := by
  simp only [E61c16words,List.all_append,E61c16p0bound]
  try rfl

theorem E61c16bounded : ∀ n ∈ E61c16words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c16wordBound

def E61c17 : Entry := ⟨1969, 12, [108,111,111,107,117,112,95,115,101,108,95,49,53,56,35,48], (.vanishing 12 none (.product (.cons (.column 57 (0)) (.cons (.column 145 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 158 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.product (.cons (.sum (.cons (.column 53 (0)) (.cons (.column 55 (0)) .nil))) (.cons (.column 175 (0)) .nil))) .nil)) .nil))))))⟩

def E61c17p0 : List Nat := [1969,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,56,35,48,0,12,0,0,42,4,1,1,57,0,1,1,145,0,1,3,0,1,1,1,158,0,0,1,3,0,1,1,4,1,2,1,1,53,0,1,1,55,0,0,1,1,175,0,0,0,0]
theorem E61c17p0bound : E61c17p0.all wordBound = true := (by decide : [1969,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,56,35,48,0,12,0,0,42,4,1,1,57,0,1,1,145,0,1,3,0,1,1,1,158,0,0,1,3,0,1,1,4,1,2,1,1,53,0,1,1,55,0,0,1,1,175,0,0,0,0].all wordBound = true)

def E61c17words : List Nat := E61c17p0

theorem E61c17wire : entryWords E61c17 = E61c17words := by
  rfl

theorem E61c17wordBound : E61c17words.all wordBound = true := by
  simp only [E61c17words,List.all_append,E61c17p0bound]
  try rfl

theorem E61c17bounded : ∀ n ∈ E61c17words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c17wordBound

def E61c18 : Entry := ⟨1970, 12, [108,111,111,107,117,112,95,115,101,108,95,49,53,56,35,49], (.vanishing 12 none (.product (.cons (.sum (.cons (.column 53 (0)) (.cons (.column 55 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 57 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 145 (0)) .nil)) .nil))))) (.cons (.column 158 (0)) .nil))))⟩

def E61c18p0 : List Nat := [1970,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,56,35,49,0,12,0,0,35,4,1,2,1,1,53,0,1,1,55,0,1,3,0,1,1,1,57,0,0,1,3,0,1,1,1,145,0,0,0,1,1,158,0,0]
theorem E61c18p0bound : E61c18p0.all wordBound = true := (by decide : [1970,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,56,35,49,0,12,0,0,35,4,1,2,1,1,53,0,1,1,55,0,1,3,0,1,1,1,57,0,0,1,3,0,1,1,1,145,0,0,0,1,1,158,0,0].all wordBound = true)

def E61c18words : List Nat := E61c18p0

theorem E61c18wire : entryWords E61c18 = E61c18words := by
  rfl

theorem E61c18wordBound : E61c18words.all wordBound = true := by
  simp only [E61c18words,List.all_append,E61c18p0bound]
  try rfl

theorem E61c18bounded : ∀ n ∈ E61c18words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c18wordBound

def E61c19 : Entry := ⟨1971, 12, [99,97,108,108,95,49,50,95,50,95,53,48], (.lookup [⟨12, (some (158)), #[103,104,105,32,33,34,35,62,63,64,28,29,30,31]⟩] [⟨50, (some (45)), #[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩])⟩

def E61c19p0 : List Nat := [1971,12,12,99,97,108,108,95,49,50,95,50,95,53,48,1,1,0,1,12,1,158,14,103,104,105,32,33,34,35,62,63,64,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem E61c19p0bound : E61c19p0.all wordBound = true := (by decide : [1971,12,12,99,97,108,108,95,49,50,95,50,95,53,48,1,1,0,1,12,1,158,14,103,104,105,32,33,34,35,62,63,64,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13].all wordBound = true)

def E61c19words : List Nat := E61c19p0

theorem E61c19wire : entryWords E61c19 = E61c19words := by
  rfl

theorem E61c19wordBound : E61c19words.all wordBound = true := by
  simp only [E61c19words,List.all_append,E61c19p0bound]
  try rfl

theorem E61c19bounded : ∀ n ∈ E61c19words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c19wordBound

def E61c20 : Entry := ⟨1972, 12, [114,97,109,95,49,50,95,50,95,57,55,95,57], (.lookup [⟨12, (some (158)), #[44,28,29,30,31,60,61]⟩] [⟨9, (some (18)), #[0,1,2,3,4,11,12]⟩])⟩

def E61c20p0 : List Nat := [1972,12,13,114,97,109,95,49,50,95,50,95,57,55,95,57,1,1,0,1,12,1,158,7,44,28,29,30,31,60,61,1,9,1,18,7,0,1,2,3,4,11,12]
theorem E61c20p0bound : E61c20p0.all wordBound = true := (by decide : [1972,12,13,114,97,109,95,49,50,95,50,95,57,55,95,57,1,1,0,1,12,1,158,7,44,28,29,30,31,60,61,1,9,1,18,7,0,1,2,3,4,11,12].all wordBound = true)

def E61c20words : List Nat := E61c20p0

theorem E61c20wire : entryWords E61c20 = E61c20words := by
  rfl

theorem E61c20wordBound : E61c20words.all wordBound = true := by
  simp only [E61c20words,List.all_append,E61c20p0bound]
  try rfl

theorem E61c20bounded : ∀ n ∈ E61c20words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c20wordBound

def E61c21 : Entry := ⟨1973, 12, [108,111,111,107,117,112,95,115,101,108,95,49,53,57,35,48], (.vanishing 12 none (.sum (.cons (.product (.cons (.column 53 (0)) (.cons (.column 55 (0)) (.cons (.column 146 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 159 (0)) .nil)) .nil))))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 53 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 55 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 146 (0)) .nil)) .nil)))) (.cons (.column 159 (0)) .nil))) .nil))))⟩

def E61c21p0 : List Nat := [1973,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,57,35,48,0,12,0,0,63,2,1,4,1,1,53,0,1,1,55,0,1,1,146,0,1,3,0,1,1,1,159,0,0,0,1,4,1,2,1,3,0,1,1,1,53,0,0,1,3,0,1,1,1,55,0,0,1,3,0,1,1,1,146,0,0,0,1,1,159,0,0,0]
theorem E61c21p0bound : E61c21p0.all wordBound = true := (by decide : [1973,12,16,108,111,111,107,117,112,95,115,101,108,95,49,53,57,35,48,0,12,0,0,63,2,1,4,1,1,53,0,1,1,55,0,1,1,146,0,1,3,0,1,1,1,159,0,0,0,1,4,1,2,1,3,0,1,1,1,53,0,0,1,3,0,1,1,1,55,0,0,1,3,0,1,1,1,146,0,0,0,1,1,159,0,0,0].all wordBound = true)

def E61c21words : List Nat := E61c21p0

theorem E61c21wire : entryWords E61c21 = E61c21words := by
  rfl

theorem E61c21wordBound : E61c21words.all wordBound = true := by
  simp only [E61c21words,List.all_append,E61c21p0bound]
  try rfl

theorem E61c21bounded : ∀ n ∈ E61c21words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c21wordBound

def E61c22 : Entry := ⟨1974, 12, [99,97,108,108,95,49,50,95,51,95,53,48], (.lookup [⟨12, (some (159)), #[106,107,108,32,33,34,35,58,59,60,28,29,30,31]⟩] [⟨50, (some (45)), #[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩])⟩

def E61c22p0 : List Nat := [1974,12,12,99,97,108,108,95,49,50,95,51,95,53,48,1,1,0,1,12,1,159,14,106,107,108,32,33,34,35,58,59,60,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem E61c22p0bound : E61c22p0.all wordBound = true := (by decide : [1974,12,12,99,97,108,108,95,49,50,95,51,95,53,48,1,1,0,1,12,1,159,14,106,107,108,32,33,34,35,58,59,60,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13].all wordBound = true)

def E61c22words : List Nat := E61c22p0

theorem E61c22wire : entryWords E61c22 = E61c22words := by
  rfl

theorem E61c22wordBound : E61c22words.all wordBound = true := by
  simp only [E61c22words,List.all_append,E61c22p0bound]
  try rfl

theorem E61c22bounded : ∀ n ∈ E61c22words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c22wordBound

def E61c23 : Entry := ⟨1975, 12, [114,97,109,95,49,50,95,51,95,52,50,95,57], (.lookup [⟨12, (some (159)), #[27,28,29,30,31,109,110]⟩] [⟨9, (some (18)), #[0,1,2,3,4,11,12]⟩])⟩

def E61c23p0 : List Nat := [1975,12,13,114,97,109,95,49,50,95,51,95,52,50,95,57,1,1,0,1,12,1,159,7,27,28,29,30,31,109,110,1,9,1,18,7,0,1,2,3,4,11,12]
theorem E61c23p0bound : E61c23p0.all wordBound = true := (by decide : [1975,12,13,114,97,109,95,49,50,95,51,95,52,50,95,57,1,1,0,1,12,1,159,7,27,28,29,30,31,109,110,1,9,1,18,7,0,1,2,3,4,11,12].all wordBound = true)

def E61c23words : List Nat := E61c23p0

theorem E61c23wire : entryWords E61c23 = E61c23words := by
  rfl

theorem E61c23wordBound : E61c23words.all wordBound = true := by
  simp only [E61c23words,List.all_append,E61c23p0bound]
  try rfl

theorem E61c23bounded : ∀ n ∈ E61c23words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c23wordBound

def E61c24 : Entry := ⟨1976, 12, [108,111,111,107,117,112,95,115,101,108,95,49,54,48,35,48], (.vanishing 12 none (.sum (.cons (.product (.cons (.column 53 (0)) (.cons (.column 146 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 160 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 55 (0)) .nil)) .nil))))) (.cons (.product (.cons (.sum (.cons (.column 55 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 53 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 146 (0)) .nil)) .nil)))) (.cons (.column 160 (0)) .nil))) .nil))))⟩

def E61c24p0 : List Nat := [1976,12,16,108,111,111,107,117,112,95,115,101,108,95,49,54,48,35,48,0,12,0,0,63,2,1,4,1,1,53,0,1,1,146,0,1,3,0,1,1,1,160,0,0,1,3,0,1,1,1,55,0,0,0,1,4,1,2,1,1,55,0,1,3,0,1,1,1,53,0,0,1,3,0,1,1,1,146,0,0,0,1,1,160,0,0,0]
theorem E61c24p0bound : E61c24p0.all wordBound = true := (by decide : [1976,12,16,108,111,111,107,117,112,95,115,101,108,95,49,54,48,35,48,0,12,0,0,63,2,1,4,1,1,53,0,1,1,146,0,1,3,0,1,1,1,160,0,0,1,3,0,1,1,1,55,0,0,0,1,4,1,2,1,1,55,0,1,3,0,1,1,1,53,0,0,1,3,0,1,1,1,146,0,0,0,1,1,160,0,0,0].all wordBound = true)

def E61c24words : List Nat := E61c24p0

theorem E61c24wire : entryWords E61c24 = E61c24words := by
  rfl

theorem E61c24wordBound : E61c24words.all wordBound = true := by
  simp only [E61c24words,List.all_append,E61c24p0bound]
  try rfl

theorem E61c24bounded : ∀ n ∈ E61c24words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c24wordBound

def E61c25 : Entry := ⟨1977, 12, [99,97,108,108,95,49,50,95,51,95,49,51], (.lookup [⟨12, (some (160)), #[111,112,28,29]⟩] [⟨13, (some (410)), #[0,1,2,3]⟩])⟩

def E61c25p0 : List Nat := [1977,12,12,99,97,108,108,95,49,50,95,51,95,49,51,1,1,0,1,12,1,160,4,111,112,28,29,1,13,1,410,4,0,1,2,3]
theorem E61c25p0bound : E61c25p0.all wordBound = true := (by decide : [1977,12,12,99,97,108,108,95,49,50,95,51,95,49,51,1,1,0,1,12,1,160,4,111,112,28,29,1,13,1,410,4,0,1,2,3].all wordBound = true)

def E61c25words : List Nat := E61c25p0

theorem E61c25wire : entryWords E61c25 = E61c25words := by
  rfl

theorem E61c25wordBound : E61c25words.all wordBound = true := by
  simp only [E61c25words,List.all_append,E61c25p0bound]
  try rfl

theorem E61c25bounded : ∀ n ∈ E61c25words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c25wordBound

def E61c26 : Entry := ⟨1978, 12, [99,97,108,108,95,49,50,95,51,95,49,53], (.lookup [⟨12, (some (160)), #[28,29,30,31]⟩] [⟨15, (some (15)), #[0,1,2,3]⟩])⟩

def E61c26p0 : List Nat := [1978,12,12,99,97,108,108,95,49,50,95,51,95,49,53,1,1,0,1,12,1,160,4,28,29,30,31,1,15,1,15,4,0,1,2,3]
theorem E61c26p0bound : E61c26p0.all wordBound = true := (by decide : [1978,12,12,99,97,108,108,95,49,50,95,51,95,49,53,1,1,0,1,12,1,160,4,28,29,30,31,1,15,1,15,4,0,1,2,3].all wordBound = true)

def E61c26words : List Nat := E61c26p0

theorem E61c26wire : entryWords E61c26 = E61c26words := by
  rfl

theorem E61c26wordBound : E61c26words.all wordBound = true := by
  simp only [E61c26words,List.all_append,E61c26p0bound]
  try rfl

theorem E61c26bounded : ∀ n ∈ E61c26words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c26wordBound

def E61c27 : Entry := ⟨1979, 12, [108,111,111,107,117,112,95,115,101,108,95,49,54,49,35,48], (.vanishing 12 none (.sum (.cons (.product (.cons (.column 57 (0)) (.cons (.column 146 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 161 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 53 (0)) .nil)) .nil))))) (.cons (.product (.cons (.sum (.cons (.column 53 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 57 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 146 (0)) .nil)) .nil)))) (.cons (.column 161 (0)) .nil))) .nil))))⟩

def E61c27p0 : List Nat := [1979,12,16,108,111,111,107,117,112,95,115,101,108,95,49,54,49,35,48,0,12,0,0,63,2,1,4,1,1,57,0,1,1,146,0,1,3,0,1,1,1,161,0,0,1,3,0,1,1,1,53,0,0,0,1,4,1,2,1,1,53,0,1,3,0,1,1,1,57,0,0,1,3,0,1,1,1,146,0,0,0,1,1,161,0,0,0]
theorem E61c27p0bound : E61c27p0.all wordBound = true := (by decide : [1979,12,16,108,111,111,107,117,112,95,115,101,108,95,49,54,49,35,48,0,12,0,0,63,2,1,4,1,1,57,0,1,1,146,0,1,3,0,1,1,1,161,0,0,1,3,0,1,1,1,53,0,0,0,1,4,1,2,1,1,53,0,1,3,0,1,1,1,57,0,0,1,3,0,1,1,1,146,0,0,0,1,1,161,0,0,0].all wordBound = true)

def E61c27words : List Nat := E61c27p0

theorem E61c27wire : entryWords E61c27 = E61c27words := by
  rfl

theorem E61c27wordBound : E61c27words.all wordBound = true := by
  simp only [E61c27words,List.all_append,E61c27p0bound]
  try rfl

theorem E61c27bounded : ∀ n ∈ E61c27words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c27wordBound

def E61c28 : Entry := ⟨1980, 12, [99,97,108,108,95,49,50,95,51,95,53,48], (.lookup [⟨12, (some (161)), #[113,114,115,32,33,34,35,58,59,60,28,29,30,31]⟩] [⟨50, (some (45)), #[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩])⟩

def E61c28p0 : List Nat := [1980,12,12,99,97,108,108,95,49,50,95,51,95,53,48,1,1,0,1,12,1,161,14,113,114,115,32,33,34,35,58,59,60,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem E61c28p0bound : E61c28p0.all wordBound = true := (by decide : [1980,12,12,99,97,108,108,95,49,50,95,51,95,53,48,1,1,0,1,12,1,161,14,113,114,115,32,33,34,35,58,59,60,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13].all wordBound = true)

def E61c28words : List Nat := E61c28p0

theorem E61c28wire : entryWords E61c28 = E61c28words := by
  rfl

theorem E61c28wordBound : E61c28words.all wordBound = true := by
  simp only [E61c28words,List.all_append,E61c28p0bound]
  try rfl

theorem E61c28bounded : ∀ n ∈ E61c28words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c28wordBound

def E61c29 : Entry := ⟨1981, 12, [114,97,109,95,49,50,95,51,95,57,56,95,57], (.lookup [⟨12, (some (161)), #[44,28,29,30,31,116,117]⟩] [⟨9, (some (18)), #[0,1,2,3,4,11,12]⟩])⟩

def E61c29p0 : List Nat := [1981,12,13,114,97,109,95,49,50,95,51,95,57,56,95,57,1,1,0,1,12,1,161,7,44,28,29,30,31,116,117,1,9,1,18,7,0,1,2,3,4,11,12]
theorem E61c29p0bound : E61c29p0.all wordBound = true := (by decide : [1981,12,13,114,97,109,95,49,50,95,51,95,57,56,95,57,1,1,0,1,12,1,161,7,44,28,29,30,31,116,117,1,9,1,18,7,0,1,2,3,4,11,12].all wordBound = true)

def E61c29words : List Nat := E61c29p0

theorem E61c29wire : entryWords E61c29 = E61c29words := by
  rfl

theorem E61c29wordBound : E61c29words.all wordBound = true := by
  simp only [E61c29words,List.all_append,E61c29p0bound]
  try rfl

theorem E61c29bounded : ∀ n ∈ E61c29words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c29wordBound

def E61c30 : Entry := ⟨1982, 12, [108,111,111,107,117,112,95,115,101,108,95,49,54,50,35,48], (.vanishing 12 none (.sum (.cons (.product (.cons (.column 57 (0)) (.cons (.column 147 (0)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 162 (0)) .nil)) .nil)))) (.cons (.product (.cons (.sum (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 57 (0)) .nil)) (.cons (.difference (.constant ⟨1, by decide⟩) (.cons (.column 147 (0)) .nil)) .nil))) (.cons (.column 162 (0)) .nil))) .nil))))⟩

def E61c30p0 : List Nat := [1982,12,16,108,111,111,107,117,112,95,115,101,108,95,49,54,50,35,48,0,12,0,0,50,2,1,4,1,1,57,0,1,1,147,0,1,3,0,1,1,1,162,0,0,0,1,4,1,2,1,3,0,1,1,1,57,0,0,1,3,0,1,1,1,147,0,0,0,1,1,162,0,0,0]
theorem E61c30p0bound : E61c30p0.all wordBound = true := (by decide : [1982,12,16,108,111,111,107,117,112,95,115,101,108,95,49,54,50,35,48,0,12,0,0,50,2,1,4,1,1,57,0,1,1,147,0,1,3,0,1,1,1,162,0,0,0,1,4,1,2,1,3,0,1,1,1,57,0,0,1,3,0,1,1,1,147,0,0,0,1,1,162,0,0,0].all wordBound = true)

def E61c30words : List Nat := E61c30p0

theorem E61c30wire : entryWords E61c30 = E61c30words := by
  rfl

theorem E61c30wordBound : E61c30words.all wordBound = true := by
  simp only [E61c30words,List.all_append,E61c30p0bound]
  try rfl

theorem E61c30bounded : ∀ n ∈ E61c30words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c30wordBound

def E61c31 : Entry := ⟨1983, 12, [99,97,108,108,95,49,50,95,52,95,53,48], (.lookup [⟨12, (some (162)), #[118,119,120,32,33,34,35,21,22,40,28,29,30,31]⟩] [⟨50, (some (45)), #[0,1,2,3,4,5,6,7,8,9,10,11,12,13]⟩])⟩

def E61c31p0 : List Nat := [1983,12,12,99,97,108,108,95,49,50,95,52,95,53,48,1,1,0,1,12,1,162,14,118,119,120,32,33,34,35,21,22,40,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem E61c31p0bound : E61c31p0.all wordBound = true := (by decide : [1983,12,12,99,97,108,108,95,49,50,95,52,95,53,48,1,1,0,1,12,1,162,14,118,119,120,32,33,34,35,21,22,40,28,29,30,31,1,50,1,45,14,0,1,2,3,4,5,6,7,8,9,10,11,12,13].all wordBound = true)

def E61c31words : List Nat := E61c31p0

theorem E61c31wire : entryWords E61c31 = E61c31words := by
  rfl

theorem E61c31wordBound : E61c31words.all wordBound = true := by
  simp only [E61c31words,List.all_append,E61c31p0bound]
  try rfl

theorem E61c31bounded : ∀ n ∈ E61c31words, n < 2^64 := by
  simpa only [List.all_eq_true, wordBound, decide_eq_true_eq] using E61c31wordBound

def E61 : List Entry := [E61c0,E61c1,E61c2,E61c3,E61c4,E61c5,E61c6,E61c7,E61c8,E61c9,E61c10,E61c11,E61c12,E61c13,E61c14,E61c15,E61c16,E61c17,E61c18,E61c19,E61c20,E61c21,E61c22,E61c23,E61c24,E61c25,E61c26,E61c27,E61c28,E61c29,E61c30,E61c31]

def E61words : List Nat := E61c0words ++ E61c1words ++ E61c2words ++ E61c3words ++ E61c4words ++ E61c5words ++ E61c6words ++ E61c7words ++ E61c8words ++ E61c9words ++ E61c10words ++ E61c11words ++ E61c12words ++ E61c13words ++ E61c14words ++ E61c15words ++ E61c16words ++ E61c17words ++ E61c18words ++ E61c19words ++ E61c20words ++ E61c21words ++ E61c22words ++ E61c23words ++ E61c24words ++ E61c25words ++ E61c26words ++ E61c27words ++ E61c28words ++ E61c29words ++ E61c30words ++ E61c31words

theorem E61wire : E61.flatMap entry.encode = E61words := by
  rw [entry_fast_fun]
  simp only [E61,List.flatMap_cons,List.flatMap_nil,List.append_nil,E61c0wire,E61c1wire,E61c2wire,E61c3wire,E61c4wire,E61c5wire,E61c6wire,E61c7wire,E61c8wire,E61c9wire,E61c10wire,E61c11wire,E61c12wire,E61c13wire,E61c14wire,E61c15wire,E61c16wire,E61c17wire,E61c18wire,E61c19wire,E61c20wire,E61c21wire,E61c22wire,E61c23wire,E61c24wire,E61c25wire,E61c26wire,E61c27wire,E61c28wire,E61c29wire,E61c30wire,E61c31wire]
  rfl

theorem E61wordBound : E61words.all wordBound = true := by
  simp only [E61words,List.all_append,E61c0wordBound,E61c1wordBound,E61c2wordBound,E61c3wordBound,E61c4wordBound,E61c5wordBound,E61c6wordBound,E61c7wordBound,E61c8wordBound,E61c9wordBound,E61c10wordBound,E61c11wordBound,E61c12wordBound,E61c13wordBound,E61c14wordBound,E61c15wordBound,E61c16wordBound,E61c17wordBound,E61c18wordBound,E61c19wordBound,E61c20wordBound,E61c21wordBound,E61c22wordBound,E61c23wordBound,E61c24wordBound,E61c25wordBound,E61c26wordBound,E61c27wordBound,E61c28wordBound,E61c29wordBound,E61c30wordBound,E61c31wordBound]
  decide

theorem E61bounded : ∀ n ∈ E61words, n < 2^64 := by
  simpa only [List.all_eq_true,wordBound,decide_eq_true_eq] using E61wordBound

theorem E61length : E61.length = 32 := by rfl

def E61selected : List RawConstraint := []
theorem E61select : (E61.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).map Entry.rule = E61selected := by rfl

def E61incoming : List RawConstraint := []
theorem E61calls : (ArtifactBinding.incomingEntries ⟨[],E61⟩).map Entry.rule = E61incoming := by rfl

theorem E61closure : (E61.filter (fun e => decide (e.owner ∈ ArtifactBinding.selectedIds))).all (fun e => (ArtifactBinding.referencedModules e).all (fun id => decide (id ∈ ArtifactBinding.selectedIds))) = true := by decide

end DivRemFV.Replay
