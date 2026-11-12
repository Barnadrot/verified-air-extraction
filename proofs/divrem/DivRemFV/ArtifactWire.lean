import DivRemFV.WireCodec
import DivRemFV.ByteWire
import DivRemFV.FastBytes

namespace DivRemFV.ArtifactWire
open NativeImport WireCodec

mutual
  theorem termDepth_le_length (t : Term) : TermWire.termDepth t ≤ (TermWire.encodeTerm t).length := by
    cases t with
    | constant v => simp [TermWire.termDepth, TermWire.encodeTerm]
    | column i s => simp [TermWire.termDepth, TermWire.encodeTerm]
    | sum a | product a =>
      have := argsDepth_le_length a
      simp only [TermWire.termDepth, TermWire.encodeTerm, List.length_cons]
      omega
    | difference h t =>
      have h1 := termDepth_le_length h
      have h2 := argsDepth_le_length t
      simp only [TermWire.termDepth, TermWire.encodeTerm, List.length_cons, List.length_append]
      omega
  theorem argsDepth_le_length (a : Args) : TermWire.argsDepth a ≤ (TermWire.encodeArgs a).length := by
    cases a with
    | nil => rfl
    | cons h t =>
      have h1 := termDepth_le_length h
      have h2 := argsDepth_le_length t
      simp only [TermWire.argsDepth, TermWire.encodeArgs, List.length_cons, List.length_append]
      omega
end

def term : Codec Term where
  encode value := (list nat).encode (TermWire.encodeTerm value)
  decode input := do
    let (tokens, rest) ← (list nat).decode input
    let (value, remaining) ← TermWire.decodeTerm tokens.length tokens
    if remaining = [] then some (value, rest) else none
  sound := by
    intro input value rest h
    obtain ⟨⟨tokens, after⟩, hv, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨parsed, remaining⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h
    split at h
    · rename_i empty; subst remaining; cases h
      have equal := TermWire.decodeTerm_sound _ _ _ _ hp
      simp only [List.append_nil] at equal
      simpa only [equal] using (list nat).sound _ _ _ hv
    · contradiction
  complete := by
    intro value rest
    have h := TermWire.decodeTerm_complete (TermWire.encodeTerm value).length value []
      (termDepth_le_length value)
    simp only [List.append_nil] at h
    simp [(list nat).complete, h]

def port : Codec Port :=
  iso (pair nat (pair (option nat) (list nat)))
    (fun v => ⟨v.1, v.2.1, v.2.2.toArray⟩)
    (fun v => (v.moduleId, v.selector, v.columns.toList))
    (by intro v; simp)
    (by intro v; cases v; simp)

abbrev ConstraintRepr :=
  Sum (Nat × Option Int × Term) (Sum (Nat × Nat × Nat)
    (Sum (List Port × List Port) (List Port × List Port)))

def fromConstraint : RawConstraint → ConstraintRepr
  | .vanishing owner domain expr => .inl (owner, domain, expr)
  | .range owner col bits => .inr (.inl (owner, col, bits))
  | .lookup sources targets => .inr (.inr (.inl (sources, targets)))
  | .bus sources targets => .inr (.inr (.inr (sources, targets)))

def toConstraint : ConstraintRepr → RawConstraint
  | .inl (owner, domain, expr) => .vanishing owner domain expr
  | .inr (.inl (owner, col, bits)) => .range owner col bits
  | .inr (.inr (.inl (sources, targets))) => .lookup sources targets
  | .inr (.inr (.inr (sources, targets))) => .bus sources targets

def constraint : Codec RawConstraint :=
  iso (sum (pair nat (pair (option integer) term))
    (sum (pair nat (pair nat nat))
      (sum (pair (list port) (list port)) (pair (list port) (list port)))))
    toConstraint fromConstraint
    (by intro v; rcases v with v | v; rfl; rcases v with v | v; rfl; cases v <;> rfl)
    (by intro v; cases v <;> rfl)

/-- Names are retained as UTF-8 bytes. They do not select the arithmetic relation. -/
structure Column where
  id : Nat
  name : List Nat
  bits : Option Nat
  input : Bool
  output : Bool
  native : Bool
  deriving DecidableEq

structure Module where
  id : Nat
  name : List Nat
  isStatic : Bool
  native : Bool
  columns : List Column
  content : List (List Nat)
  deriving DecidableEq

structure Entry where
  id : Nat
  owner : Nat
  name : List Nat
  rule : RawConstraint

structure Artifact where
  modules : List Module
  entries : List Entry

def column : Codec Column :=
  iso (pair nat (pair (list nat) (pair (option nat) (pair boolean (pair boolean boolean)))))
    (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩)
    (fun v => (v.id, v.name, v.bits, v.input, v.output, v.native))
    (by intro v; rfl) (by intro v; rfl)

def module : Codec Module :=
  iso (pair nat (pair (list nat) (pair boolean (pair boolean (pair (list column) (list (list nat)))))))
    (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2⟩)
    (fun v => (v.id, v.name, v.isStatic, v.native, v.columns, v.content))
    (by intro v; rfl) (by intro v; rfl)

theorem module_encoding (m : Module) : module.encode m =
    [m.id] ++ (WireCodec.list WireCodec.nat).encode m.name ++
      WireCodec.boolean.encode m.isStatic ++ WireCodec.boolean.encode m.native ++
      (WireCodec.list column).encode m.columns ++
      (WireCodec.list (WireCodec.list WireCodec.nat)).encode m.content := by
  simp [module, WireCodec.iso, WireCodec.pair, WireCodec.nat, List.append_assoc]

def entry : Codec Entry :=
  iso (pair nat (pair nat (pair (list nat) constraint)))
    (fun v => ⟨v.1, v.2.1, v.2.2.1, v.2.2.2⟩)
    (fun v => (v.id, v.owner, v.name, v.rule))
    (by intro v; rfl) (by intro v; rfl)

/-- Magic, format version and field modulus are checked, not inferred from data. -/
def artifact : Codec Artifact :=
  iso (pair (fixed 1146242647) (pair (fixed 1) (pair (fixed fieldModulus)
    (pair (list module) (list entry)))))
    (fun v => ⟨v.2.2.2.1, v.2.2.2.2⟩)
    (fun v => ((), (), (), v.modules, v.entries))
    (by intro ⟨⟨⟩, ⟨⟨⟩, ⟨⟨⟩, v⟩⟩⟩; rfl)
    (by intro v; rfl)

def decode (bytes : List UInt8) : Option Artifact := do
  let words ← ByteWire.readWordsFast bytes
  read artifact words

/-- Independent grammar for the complete artifact, including static contents. -/
def Encodes (bytes : List UInt8) (value : Artifact) : Prop :=
  ByteWire.Words bytes (artifact.encode value)

theorem decode_iff (bytes : List UInt8) (value : Artifact) :
    decode bytes = some value ↔ Encodes bytes value := by
  constructor
  · intro h
    obtain ⟨words, parsed, decoded⟩ := Option.bind_eq_some_iff.mp h
    have equal := (read_iff artifact words value).1 decoded
    unfold Encodes
    rw [← equal]
    rw [ByteWire.readWordsFast_eq] at parsed
    exact ByteWire.readWords_sound bytes words parsed
  · intro h
    simp [decode, ByteWire.readWordsFast_eq, ByteWire.readWords_complete h, (read_iff artifact _ value).2 rfl]

theorem unambiguous (bytes : List UInt8) (a b : Artifact)
    (ha : Encodes bytes a) (hb : Encodes bytes b) : a = b := by
  have h := (decode_iff bytes a).2 ha
  rw [(decode_iff bytes b).2 hb] at h
  exact (Option.some.inj h).symm

def Artifact.rawConstraints (a : Artifact) : List RawConstraint := a.entries.map Entry.rule

theorem artifact_encoding (m : List Module) (e : List Entry) :
    artifact.encode ⟨m,e⟩ =
      [1146242647, 1, fieldModulus, m.length] ++ m.flatMap module.encode ++
        e.length :: e.flatMap entry.encode := by
  simp [artifact, WireCodec.iso, WireCodec.pair, WireCodec.fixed, WireCodec.list,
    List.append_assoc]

theorem decoded_semantics (bytes : List UInt8) (value : Artifact)
    (h : decode bytes = some value) (tables : Tables) :
    Encodes bytes value ∧
      (ConstraintsHold tables (value.rawConstraints.map RawConstraint.translate) ↔
       RawConstraintsHold tables value.rawConstraints) :=
  ⟨(decode_iff bytes value).1 h, translate_constraints_holds _ _⟩

end DivRemFV.ArtifactWire
