import DivRemFV.ByteWire

namespace DivRemFV.ByteWire

def writeWord (n : Nat) : List UInt8 :=
  [UInt8.ofNat n, UInt8.ofNat (n/256), UInt8.ofNat (n/65536),
    UInt8.ofNat (n/16777216), UInt8.ofNat (n/4294967296),
    UInt8.ofNat (n/1099511627776), UInt8.ofNat (n/281474976710656),
    UInt8.ofNat (n/72057594037927936)]

theorem wordValue_writeWord (n : Nat) (h : n < 2^64) :
    wordValue (UInt8.ofNat n) (UInt8.ofNat (n/256)) (UInt8.ofNat (n/65536))
      (UInt8.ofNat (n/16777216)) (UInt8.ofNat (n/4294967296))
      (UInt8.ofNat (n/1099511627776)) (UInt8.ofNat (n/281474976710656))
      (UInt8.ofNat (n/72057594037927936)) = n := by
  simp only [wordValue, UInt8.toNat_ofNat']
  omega

def writeWords (words : List Nat) : List UInt8 := words.flatMap writeWord

theorem writeWords_encodes (words : List Nat) (bounded : ∀ n ∈ words, n < 2^64) :
    Words (writeWords words) words := by
  induction words with
  | nil => exact Words.nil
  | cons n ns ih =>
    have hn := bounded n (by simp)
    have tail := ih (fun v member => bounded v (by simp [member]))
    have step := Words.cons (UInt8.ofNat n) (UInt8.ofNat (n/256)) (UInt8.ofNat (n/65536))
      (UInt8.ofNat (n/16777216)) (UInt8.ofNat (n/4294967296))
      (UInt8.ofNat (n/1099511627776)) (UInt8.ofNat (n/281474976710656))
      (UInt8.ofNat (n/72057594037927936)) (writeWords ns) ns tail
    rw [wordValue_writeWord n hn] at step
    exact step

theorem writeWords_readWords (bytes : List UInt8) (words : List Nat)
    (accepted : readWords bytes = some words) : writeWords words = bytes := by
  have grammar := readWords_sound bytes words accepted
  clear accepted
  induction grammar with
  | nil => rfl
  | cons a b c d e f g h bytes words tail ih =>
    simp only [writeWords, List.flatMap_cons, writeWord, wordValue, UInt8.toNat_ofNat',
      List.cons_append, List.nil_append]
    have ha := a.toNat_lt_size
    have hb := b.toNat_lt_size
    have hc := c.toNat_lt_size
    have hd := d.toNat_lt_size
    have he := e.toNat_lt_size
    have hf := f.toNat_lt_size
    have hg := g.toNat_lt_size
    have hh := h.toNat_lt_size
    change a.toNat < 256 at ha
    change b.toNat < 256 at hb
    change c.toNat < 256 at hc
    change d.toNat < 256 at hd
    change e.toNat < 256 at he
    change f.toNat < 256 at hf
    change g.toNat < 256 at hg
    change h.toNat < 256 at hh
    change words.flatMap writeWord = bytes at ih
    rw [ih]
    simp only [List.cons.injEq, ← UInt8.toNat_inj, UInt8.toNat_ofNat']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

end DivRemFV.ByteWire
