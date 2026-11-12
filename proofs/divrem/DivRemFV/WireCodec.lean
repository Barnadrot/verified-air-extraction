import DivRemFV.TermWire

namespace DivRemFV.WireCodec

/-- A prefix codec. Successful parsing consumes exactly the specified encoding. -/
structure Codec (α : Type) where
  encode : α → List Nat
  decode : List Nat → Option (α × List Nat)
  sound : ∀ input value rest, decode input = some (value, rest) →
    input = encode value ++ rest
  complete : ∀ value rest, decode (encode value ++ rest) = some (value, rest)

def nat : Codec Nat where
  encode n := [n]
  decode | n :: rest => some (n, rest) | [] => none
  sound := by intro input value rest h; cases input <;> simp_all
  complete := by intros; rfl

def fixed (tag : Nat) : Codec Unit where
  encode _ := [tag]
  decode | n :: rest => if n = tag then some ((), rest) else none | [] => none
  sound := by
    intro input value rest h
    cases input with
    | nil => simp_all
    | cons n tail => split at h <;> simp_all
  complete := by intros; simp

def pair (a : Codec α) (b : Codec β) : Codec (α × β) where
  encode v := a.encode v.1 ++ b.encode v.2
  decode input := do
    let (x, rest) ← a.decode input
    let (y, rest) ← b.decode rest
    some ((x, y), rest)
  sound := by
    intro input value rest h
    obtain ⟨⟨x, afterX⟩, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨y, afterY⟩, hy, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    rw [a.sound _ _ _ hx, b.sound _ _ _ hy]
    simp [List.append_assoc]
  complete := by
    intro value rest
    simp [List.append_assoc, a.complete, b.complete]

def iso (codec : Codec α) (forward : α → β) (backward : β → α)
    (left : ∀ x, backward (forward x) = x) (right : ∀ x, forward (backward x) = x) : Codec β where
  encode v := codec.encode (backward v)
  decode input := do
    let (v, rest) ← codec.decode input
    some (forward v, rest)
  sound := by
    intro input value rest h
    obtain ⟨⟨v, tail⟩, hv, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    simpa only [left] using codec.sound _ _ _ hv
  complete := by intro value rest; simp [codec.complete, right]

def sum (a : Codec α) (b : Codec β) : Codec (Sum α β) where
  encode | .inl v => 0 :: a.encode v | .inr v => 1 :: b.encode v
  decode
    | 0 :: rest => do let (v, tail) ← a.decode rest; some (.inl v, tail)
    | 1 :: rest => do let (v, tail) ← b.decode rest; some (.inr v, tail)
    | _ => none
  sound := by
    intro input value rest h
    cases input with
    | nil => simp_all
    | cons tag tail =>
      cases tag with
      | zero =>
        obtain ⟨⟨v, after⟩, hv, h⟩ := Option.bind_eq_some_iff.mp h
        cases h
        exact congrArg (0 :: ·) (a.sound _ _ _ hv)
      | succ tag =>
        cases tag with
        | zero =>
          obtain ⟨⟨v, after⟩, hv, h⟩ := Option.bind_eq_some_iff.mp h
          cases h
          exact congrArg (1 :: ·) (b.sound _ _ _ hv)
        | succ tag => simp_all
  complete := by intro value rest; cases value <;> simp_all [a.complete, b.complete]

def option (a : Codec α) : Codec (Option α) :=
  iso (sum (fixed 0) a)
    (fun v => match v with | .inl _ => none | .inr x => some x)
    (fun v => match v with | none => .inl () | some x => .inr x)
    (by intro v; cases v with | inl u => cases u; rfl | inr x => rfl)
    (by intro v; cases v <;> rfl)

def boolean : Codec Bool :=
  iso (sum (fixed 0) (fixed 0))
    (fun v => match v with | .inl _ => false | .inr _ => true)
    (fun v => if v then .inr () else .inl ())
    (by intro v; cases v with | inl u => cases u; rfl | inr u => cases u; rfl)
    (by intro v; cases v <;> rfl)

def integer : Codec Int := iso nat TermWire.decodeInt TermWire.encodeInt
  TermWire.encodeInt_decodeInt TermWire.decodeInt_encodeInt

def decodeMany (a : Codec α) : Nat → List Nat → Option (List α × List Nat)
  | 0, input => some ([], input)
  | n + 1, input => do
    let (v, rest) ← a.decode input
    let (vs, rest) ← decodeMany a n rest
    some (v :: vs, rest)

theorem decodeMany_sound (a : Codec α) (n : Nat) (input : List Nat)
    (values : List α) (rest : List Nat) (h : decodeMany a n input = some (values, rest)) :
    values.length = n ∧ input = values.flatMap a.encode ++ rest := by
  induction n generalizing input values with
  | zero => cases h; simp
  | succ n ih =>
    obtain ⟨⟨v, after⟩, hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨vs, tail⟩, hvs, h⟩ := Option.bind_eq_some_iff.mp h
    cases h
    obtain ⟨len, encoded⟩ := ih _ _ hvs
    constructor
    · simp [len]
    · rw [a.sound _ _ _ hv, encoded]; simp [List.append_assoc]

theorem decodeMany_complete (a : Codec α) (values : List α) (rest : List Nat) :
    decodeMany a values.length (values.flatMap a.encode ++ rest) = some (values, rest) := by
  induction values with
  | nil => rfl
  | cons v vs ih => simp [decodeMany, List.append_assoc, a.complete, ih]

def decodeManyRev (a : Codec α) : Nat → List Nat → List α → Option (List α × List Nat)
  | 0, input, acc => some (acc.reverse, input)
  | n + 1, input, acc => do
    let (v, rest) ← a.decode input
    decodeManyRev a n rest (v :: acc)

theorem decodeManyRev_eq (a : Codec α) (n : Nat) (input : List Nat) (acc : List α) :
    decodeManyRev a n input acc =
      (decodeMany a n input).map (fun v => (acc.reverse ++ v.1, v.2)) := by
  induction n generalizing input acc with
  | zero => simp [decodeManyRev, decodeMany]
  | succ n ih =>
    simp only [decodeManyRev, decodeMany]
    cases decoded : a.decode input with
    | none => simp
    | some p =>
      rcases p with ⟨v, rest⟩
      change decodeManyRev a n rest (v :: acc) =
        ((decodeMany a n rest).bind (fun q => some (v :: q.1, q.2))).map
          (fun q => (acc.reverse ++ q.1, q.2))
      rw [ih]
      cases decodeMany a n rest <;> simp [List.reverse_cons, List.append_assoc]

def list (a : Codec α) : Codec (List α) where
  encode vs := vs.length :: vs.flatMap a.encode
  decode | n :: rest => decodeManyRev a n rest [] | [] => none
  sound := by
    intro input values rest h
    cases input with
    | nil => simp_all
    | cons n tail =>
      simp only [decodeManyRev_eq, List.reverse_nil, List.nil_append, Prod.eta] at h
      rw [Option.map_id'] at h
      obtain ⟨len, encoded⟩ := decodeMany_sound a n tail values rest h
      simp [len, encoded]
  complete := by
    intro values rest
    simpa [decodeManyRev_eq] using decodeMany_complete a values rest

def read (codec : Codec α) (input : List Nat) : Option α := do
  let (v, rest) ← codec.decode input
  if rest = [] then some v else none

theorem read_iff (codec : Codec α) (input : List Nat) (value : α) :
    read codec input = some value ↔ input = codec.encode value := by
  constructor
  · intro h
    obtain ⟨⟨v, rest⟩, hv, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · rename_i empty; subst rest; cases h
      simpa using codec.sound _ _ _ hv
    · contradiction
  · rintro rfl
    have h := codec.complete value []
    simp only [List.append_nil] at h
    simp [read, h]

theorem unambiguous (codec : Codec α) (input : List Nat) (a b : α)
    (ha : input = codec.encode a) (hb : input = codec.encode b) : a = b := by
  have h := (read_iff codec input a).2 ha
  rw [(read_iff codec input b).2 hb] at h
  exact (Option.some.inj h).symm

end DivRemFV.WireCodec
