import DivRemFV.TermWire

namespace DivRemFV.ByteWire
open NativeImport

/-- The numerical meaning of eight bytes in little-endian order. -/
def wordValue (a b c d e f g h : UInt8) : Nat :=
  a.toNat + 256*b.toNat + 65536*c.toNat + 16777216*d.toNat +
    4294967296*e.toNat + 1099511627776*f.toNat +
    281474976710656*g.toNat + 72057594037927936*h.toNat

theorem wordValue_bound (a b c d e f g h : UInt8) : wordValue a b c d e f g h < 2^64 := by
  have ha : a.toNat < 256 := a.toNat_lt_size
  have hb : b.toNat < 256 := b.toNat_lt_size
  have hc : c.toNat < 256 := c.toNat_lt_size
  have hd : d.toNat < 256 := d.toNat_lt_size
  have he : e.toNat < 256 := e.toNat_lt_size
  have hf : f.toNat < 256 := f.toNat_lt_size
  have hg : g.toNat < 256 := g.toNat_lt_size
  have hh : h.toNat < 256 := h.toNat_lt_size
  unfold wordValue
  omega

/-- Independent byte grammar. Each word has exactly eight bytes. -/
inductive Words : List UInt8 → List Nat → Prop where
  | nil : Words [] []
  | cons (a b c d e f g h : UInt8) (bytes : List UInt8) (words : List Nat)
      (tail : Words bytes words) :
      Words (a::b::c::d::e::f::g::h::bytes) (wordValue a b c d e f g h :: words)

def readWords : List UInt8 → Option (List Nat)
  | [] => some []
  | a::b::c::d::e::f::g::h::tail => do
    let words ← readWords tail
    some (wordValue a b c d e f g h :: words)
  | _ => none

theorem readWords_sound (bytes : List UInt8) (words : List Nat)
    (accepted : readWords bytes = some words) : Words bytes words := by
  fun_induction readWords bytes generalizing words with
  | case1 =>
    cases accepted
    exact Words.nil
  | case2 a b c d e f g h tail ih =>
    change (readWords tail).bind (fun ws => some (wordValue a b c d e f g h :: ws)) = some words at accepted
    obtain ⟨ws, decoded, equal⟩ := Option.bind_eq_some_iff.mp accepted
    cases equal
    exact Words.cons a b c d e f g h tail ws (ih ws decoded)
  | case3 => simp_all

theorem readWords_complete {bytes : List UInt8} {words : List Nat}
    (encoded : Words bytes words) : readWords bytes = some words := by
  induction encoded with
  | nil => rfl
  | cons a b c d e f g h bytes words tail ih =>
    simp [readWords, ih]

theorem readWords_iff (bytes : List UInt8) (words : List Nat) :
    readWords bytes = some words ↔ Words bytes words :=
  ⟨readWords_sound bytes words, readWords_complete⟩

theorem Words.bounded {bytes : List UInt8} {words : List Nat}
    (encoded : Words bytes words) : ∀ value ∈ words, value < 2^64 := by
  induction encoded with
  | nil => simp
  | cons a b c d e f g h bytes words tail ih =>
    intro value member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact wordValue_bound a b c d e f g h
    · exact ih value member

theorem Words.length {bytes : List UInt8} {words : List Nat}
    (encoded : Words bytes words) : bytes.length = 8 * words.length := by
  induction encoded with
  | nil => rfl
  | cons a b c d e f g h bytes words tail ih => simp_all [Nat.mul_add]

theorem rejects_partial_word (bytes : List UInt8) (invalid : bytes.length % 8 ≠ 0) :
    readWords bytes = none := by
  cases result : readWords bytes with
  | none => rfl
  | some words =>
    have h := (readWords_sound bytes words result).length
    rw [h, Nat.mul_mod_right] at invalid
    contradiction

def readTerm (fuel : Nat) (bytes : List UInt8) : Option Term := do
  let words ← readWords bytes
  let (term, rest) ← TermWire.decodeTerm fuel words
  if rest = [] then some term else none

/-- A byte sequence is a term encoding exactly when its words follow the term grammar. -/
def EncodesTerm (bytes : List UInt8) (term : Term) : Prop :=
  Words bytes (TermWire.encodeTerm term)

theorem readTerm_sound (fuel : Nat) (bytes : List UInt8) (term : Term)
    (accepted : readTerm fuel bytes = some term) : EncodesTerm bytes term := by
  change (readWords bytes).bind (fun ws =>
    (TermWire.decodeTerm fuel ws).bind (fun p => if p.2 = [] then some p.1 else none)) = some term at accepted
  obtain ⟨words, decoded, remaining⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨⟨parsed, rest⟩, parsedOk, remaining⟩ := Option.bind_eq_some_iff.mp remaining
  dsimp only at remaining
  split at remaining
  · rename_i empty
    subst rest
    cases remaining
    have equal := TermWire.decodeTerm_sound fuel words term [] parsedOk
    simp only [List.append_nil] at equal
    unfold EncodesTerm
    rw [← equal]
    exact readWords_sound bytes words decoded
  · contradiction

theorem readTerm_complete (fuel : Nat) (bytes : List UInt8) (term : Term)
    (encoded : EncodesTerm bytes term) (enough : TermWire.termDepth term ≤ fuel) :
    readTerm fuel bytes = some term := by
  have decoded := readWords_complete encoded
  have parsed := TermWire.decodeTerm_complete fuel term [] enough
  simp only [List.append_nil] at parsed
  simp [readTerm, decoded, parsed]

theorem readTerm_iff (fuel : Nat) (bytes : List UInt8) (term : Term)
    (enough : TermWire.termDepth term ≤ fuel) :
    readTerm fuel bytes = some term ↔ EncodesTerm bytes term :=
  ⟨readTerm_sound fuel bytes term, fun encoded => readTerm_complete fuel bytes term encoded enough⟩

end DivRemFV.ByteWire
