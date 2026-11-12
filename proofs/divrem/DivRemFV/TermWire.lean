import DivRemFV.NativeImport

namespace DivRemFV.TermWire
open NativeImport

-- Tags: constant=0, column=1, sum=2, difference=3, product=4.
-- Argument lists use nil=0 and cons=1. Signed shifts use zigzag encoding.
def encodeInt (value : Int) : Nat :=
  if value < 0 then 2 * (-value).toNat - 1 else 2 * value.toNat

def decodeInt (value : Nat) : Int :=
  if value % 2 = 0 then (value / 2 : Nat) else -((value / 2 + 1 : Nat) : Int)

theorem decodeInt_encodeInt (value : Int) : decodeInt (encodeInt value) = value := by
  unfold decodeInt encodeInt
  split <;> split <;> omega

theorem encodeInt_decodeInt (value : Nat) : encodeInt (decodeInt value) = value := by
  unfold decodeInt encodeInt
  split <;> split <;> omega

theorem decodeInt_bounds (value : Nat) (bounded : value < 2^64) :
    -(2^63) ≤ decodeInt value ∧ decodeInt value < 2^63 := by
  unfold decodeInt
  split <;> omega

mutual
  def encodeTerm : Term → List Nat
    | .constant value => [0, value.val]
    | .column id shift => [1, id, encodeInt shift]
    | .sum args => 2 :: encodeArgs args
    | .difference first rest => 3 :: (encodeTerm first ++ encodeArgs rest)
    | .product args => 4 :: encodeArgs args
  def encodeArgs : Args → List Nat
    | .nil => [0]
    | .cons head tail => 1 :: (encodeTerm head ++ encodeArgs tail)
end

mutual
  def decodeTerm : Nat → List Nat → Option (Term × List Nat)
    | 0, _ => none
    | _ + 1, 0 :: value :: tail =>
      if bound : value < fieldModulus then some (.constant ⟨value, bound⟩, tail) else none
    | _ + 1, 1 :: id :: shift :: tail => some (.column id (decodeInt shift), tail)
    | fuel + 1, 2 :: tail => do
      let (args, rest) ← decodeArgs fuel tail
      some (.sum args, rest)
    | fuel + 1, 3 :: tail => do
      let (first, rest) ← decodeTerm fuel tail
      let (args, rest) ← decodeArgs fuel rest
      some (.difference first args, rest)
    | fuel + 1, 4 :: tail => do
      let (args, rest) ← decodeArgs fuel tail
      some (.product args, rest)
    | _ + 1, _ => none
  def decodeArgs : Nat → List Nat → Option (Args × List Nat)
    | 0, _ => none
    | _ + 1, 0 :: tail => some (.nil, tail)
    | fuel + 1, 1 :: tail => do
      let (head, rest) ← decodeTerm fuel tail
      let (args, rest) ← decodeArgs fuel rest
      some (.cons head args, rest)
    | _ + 1, _ => none
end

private theorem decode_sound (fuel : Nat) :
    (∀ input term rest, decodeTerm fuel input = some (term, rest) →
      input = encodeTerm term ++ rest) ∧
    (∀ input args rest, decodeArgs fuel input = some (args, rest) →
      input = encodeArgs args ++ rest) := by
  induction fuel with
  | zero => simp [decodeTerm, decodeArgs]
  | succ fuel ih =>
    constructor
    · intro input term rest accepted
      cases input with
      | nil => simp [decodeTerm] at accepted
      | cons tag tail =>
        cases tag with
        | zero =>
          cases tail with
          | nil => simp [decodeTerm] at accepted
          | cons value tail =>
            simp only [decodeTerm] at accepted
            split at accepted
            · cases accepted
              rfl
            · contradiction
        | succ tag =>
          cases tag with
          | zero =>
            cases tail with
            | nil => simp [decodeTerm] at accepted
            | cons id tail =>
              cases tail with
              | nil => simp [decodeTerm] at accepted
              | cons shift tail =>
                cases accepted
                simp [encodeTerm, encodeInt_decodeInt]
          | succ tag =>
            cases tag with
            | zero =>
              change (decodeArgs fuel tail).bind (fun p => some (.sum p.1, p.2)) = some (term, rest) at accepted
              obtain ⟨⟨args, remainder⟩, decoded, equal⟩ := Option.bind_eq_some_iff.mp accepted
              cases equal
              simpa [encodeTerm] using congrArg (2 :: ·) (ih.2 _ _ _ decoded)
            | succ tag =>
              cases tag with
              | zero =>
                change (decodeTerm fuel tail).bind (fun p =>
                  (decodeArgs fuel p.2).bind (fun q => some (.difference p.1 q.1, q.2))) = some (term, rest) at accepted
                obtain ⟨⟨first, afterFirst⟩, firstDecoded, remaining⟩ := Option.bind_eq_some_iff.mp accepted
                obtain ⟨⟨args, afterArgs⟩, argsDecoded, equal⟩ := Option.bind_eq_some_iff.mp remaining
                cases equal
                dsimp only at argsDecoded ⊢
                rw [ih.1 _ _ _ firstDecoded, ih.2 _ _ _ argsDecoded]
                simp [encodeTerm, List.append_assoc]
              | succ tag =>
                cases tag with
                | zero =>
                  change (decodeArgs fuel tail).bind (fun p => some (.product p.1, p.2)) = some (term, rest) at accepted
                  obtain ⟨⟨args, remainder⟩, decoded, equal⟩ := Option.bind_eq_some_iff.mp accepted
                  cases equal
                  simpa [encodeTerm] using congrArg (4 :: ·) (ih.2 _ _ _ decoded)
                | succ tag => simp [decodeTerm] at accepted
    · intro input args rest accepted
      cases input with
      | nil => simp [decodeArgs] at accepted
      | cons tag tail =>
        cases tag with
        | zero =>
          cases accepted
          rfl
        | succ tag =>
          cases tag with
          | zero =>
            change (decodeTerm fuel tail).bind (fun p =>
              (decodeArgs fuel p.2).bind (fun q => some (.cons p.1 q.1, q.2))) = some (args, rest) at accepted
            obtain ⟨⟨head, afterHead⟩, headDecoded, remaining⟩ := Option.bind_eq_some_iff.mp accepted
            obtain ⟨⟨tail, afterTail⟩, tailDecoded, equal⟩ := Option.bind_eq_some_iff.mp remaining
            cases equal
            dsimp only at tailDecoded ⊢
            rw [ih.1 _ _ _ headDecoded, ih.2 _ _ _ tailDecoded]
            simp [encodeArgs, List.append_assoc]
          | succ tag => simp [decodeArgs] at accepted

theorem decodeTerm_sound (fuel : Nat) (input : List Nat) (term : Term) (rest : List Nat)
    (accepted : decodeTerm fuel input = some (term, rest)) :
    input = encodeTerm term ++ rest := (decode_sound fuel).1 _ _ _ accepted

theorem decodeArgs_sound (fuel : Nat) (input : List Nat) (args : Args) (rest : List Nat)
    (accepted : decodeArgs fuel input = some (args, rest)) :
    input = encodeArgs args ++ rest := (decode_sound fuel).2 _ _ _ accepted

theorem rejects_noncanonical_constant (fuel value : Nat) (tail : List Nat)
    (invalid : fieldModulus ≤ value) : decodeTerm fuel (0 :: value :: tail) = none := by
  cases fuel <;> simp [decodeTerm, Nat.not_lt.mpr invalid]

mutual
  def termDepth : Term → Nat
    | .constant _ | .column _ _ => 1
    | .sum args | .product args => 1 + argsDepth args
    | .difference first rest => 1 + max (termDepth first) (argsDepth rest)
  def argsDepth : Args → Nat
    | .nil => 1
    | .cons head tail => 1 + max (termDepth head) (argsDepth tail)
end

mutual
  theorem decodeTerm_complete (fuel : Nat) (term : Term) (rest : List Nat)
      (enough : termDepth term ≤ fuel) :
      decodeTerm fuel (encodeTerm term ++ rest) = some (term, rest) := by
    cases fuel with
    | zero => cases term <;> simp [termDepth] at enough
    | succ fuel =>
      cases term with
      | constant value => simp [encodeTerm, decodeTerm, value.isLt]
      | column id shift => simp [encodeTerm, decodeTerm, decodeInt_encodeInt]
      | sum args =>
        have h : argsDepth args ≤ fuel := by simp [termDepth] at enough; omega
        simp [encodeTerm, decodeTerm, decodeArgs_complete fuel args rest h]
      | product args =>
        have h : argsDepth args ≤ fuel := by simp [termDepth] at enough; omega
        simp [encodeTerm, decodeTerm, decodeArgs_complete fuel args rest h]
      | difference first tail =>
        have h1 : termDepth first ≤ fuel := by simp [termDepth] at enough; omega
        have h2 : argsDepth tail ≤ fuel := by simp [termDepth] at enough; omega
        simp [encodeTerm, decodeTerm, List.append_assoc,
          decodeTerm_complete fuel first (encodeArgs tail ++ rest) h1,
          decodeArgs_complete fuel tail rest h2]
  theorem decodeArgs_complete (fuel : Nat) (args : Args) (rest : List Nat)
      (enough : argsDepth args ≤ fuel) :
      decodeArgs fuel (encodeArgs args ++ rest) = some (args, rest) := by
    cases fuel with
    | zero => cases args <;> simp [argsDepth] at enough
    | succ fuel =>
      cases args with
      | nil => rfl
      | cons head tail =>
        have h1 : termDepth head ≤ fuel := by simp [argsDepth] at enough; omega
        have h2 : argsDepth tail ≤ fuel := by simp [argsDepth] at enough; omega
        simp [encodeArgs, decodeArgs, List.append_assoc,
          decodeTerm_complete fuel head (encodeArgs tail ++ rest) h1,
          decodeArgs_complete fuel tail rest h2]
end

/-- Acceptance is equivalent to the independent prefix grammar, with sufficient parser fuel. -/
theorem decodeTerm_iff (fuel : Nat) (input : List Nat) (term : Term) (rest : List Nat)
    (enough : termDepth term ≤ fuel) :
    decodeTerm fuel input = some (term, rest) ↔ input = encodeTerm term ++ rest := by
  constructor
  · exact decodeTerm_sound fuel input term rest
  · intro equal
    rw [equal]
    exact decodeTerm_complete fuel term rest enough

/-- Decoding feeds the existing semantic-preservation theorem without a second expression model. -/
theorem decoded_translation (fuel : Nat) (input : List Nat) (term : Term) (rest : List Nat)
    (accepted : decodeTerm fuel input = some (term, rest))
    (tables : Tables) (moduleId : Nat) (row : Int) :
    input = encodeTerm term ++ rest ∧
      term.translate.evalField tables moduleId row = term.eval tables moduleId row :=
  ⟨decodeTerm_sound fuel input term rest accepted, Term.translate_eval tables moduleId row term⟩

end DivRemFV.TermWire
