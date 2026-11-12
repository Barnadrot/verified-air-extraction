import DivRemFV.ArtifactWire
import DivRemFV.BoundSigned64
import DivRemFV.Generated.Incoming

namespace DivRemFV.ArtifactBinding
open NativeImport ArtifactWire

def dynamicWidths : List (Nat × Nat) :=
  [(55,28), (56,14), (61,123), (62,47), (63,53), (64,27), (65,30), (66,16)]

def selectedIds : List Nat := dynamicWidths.map Prod.fst ++ rangeTablePairs.map Prod.fst

def selectedEntries (full : Artifact) : List Entry :=
  full.entries.filter fun entry => decide (entry.owner ∈ selectedIds)

def selectedRaw (full : Artifact) : List RawConstraint :=
  (selectedEntries full).map Entry.rule

def incomingEntries (full : Artifact) : List Entry :=
  full.entries.filter fun entry => match entry.rule with
    | .lookup _ targets => targets.any fun port => decide (port.moduleId ∈ [61,62,63,64])
    | _ => false

def referencedModules (entry : Entry) : List Nat := entry.owner :: (match entry.rule with
  | .lookup sources targets | .bus sources targets => (sources ++ targets).map Port.moduleId
  | .vanishing owner _ _ | .range owner _ _ => [owner])

def indexCheck (full : Artifact) : Bool :=
  decide (full.modules.map Module.id = List.range full.modules.length) &&
  decide (full.entries.map Entry.id = List.range full.entries.length)

def dynamicCheck (full : Artifact) : Bool := dynamicWidths.all fun (id, width) =>
  match full.modules.find? (fun m => decide (m.id = id)) with
  | none => false
  | some m => !m.isStatic && decide (m.columns.length = width) &&
      decide (m.columns.map Column.id = List.range width) && decide (m.content = [])

def rangeContent (bits : Nat) : List (List Nat) := (List.range (2^bits)).map (fun n => [n])

def rangeCheck (full : Artifact) : Bool := rangeTablePairs.all fun (id, bits) =>
  match full.modules.find? (fun m => decide (m.id = id)) with
  | none => false
  | some m => m.isStatic && decide (m.columns.length = 1) &&
      decide (m.content = rangeContent bits)

def closureCheck (full : Artifact) : Bool := (selectedEntries full).all fun entry =>
  (referencedModules entry).all fun id => decide (id ∈ selectedIds)

/-- The selector is computed from the full artifact, never supplied by Go. -/
def check (full : Artifact) : Bool :=
  indexCheck full && dynamicCheck full && rangeCheck full && closureCheck full &&
  Binding.check (selectedRaw full) Generated.constraints &&
  Binding.check ((incomingEntries full).map Entry.rule) Generated.incomingConstraints

theorem owned_coverage (full : Artifact) (entry : Entry) :
    entry ∈ selectedEntries full ↔ entry ∈ full.entries ∧ entry.owner ∈ selectedIds := by
  simp [selectedEntries]

theorem check_component (full : Artifact) (h : check full = true) :
    Binding.check (selectedRaw full) Generated.constraints = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.1.2

theorem check_interfaces (full : Artifact) (h : check full = true) :
    Binding.check ((incomingEntries full).map Entry.rule) Generated.incomingConstraints = true := by
  simp only [check, Bool.and_eq_true] at h
  exact h.2

theorem check_closure (full : Artifact) (h : check full = true) :
    ∀ entry ∈ selectedEntries full, ∀ id ∈ referencedModules entry, id ∈ selectedIds := by
  simp only [check, Bool.and_eq_true] at h
  have closed := h.1.1.2
  simpa only [closureCheck, List.all_eq_true, decide_eq_true_eq] using closed

def toRow (values : List Nat) : Row :=
  (values.map fun value => (⟨value % fieldModulus, Nat.mod_lt _ (by decide)⟩ : Scalar)).toArray

def StaticHolds (full : Artifact) (tables : Tables) : Prop :=
  ∀ m ∈ full.modules, m.isStatic = true → tables m.id = (m.content.map toRow).toArray

theorem checked_ranges_fixed (full : Artifact) (h : rangeCheck full = true)
    (tables : Tables) (fixed : StaticHolds full tables) : StaticTablesFixed tables := by
  intro id bits member
  have ranges := List.all_eq_true.mp h (id,bits) member
  dsimp only at ranges
  cases found : full.modules.find? (fun m => decide (m.id = id)) with
  | none => simp [found] at ranges
  | some m =>
    rw [found] at ranges
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ranges
    have ident : m.id = id := by simpa using List.find?_some found
    have stat := fixed m (List.mem_of_find?_eq_some found) ranges.1.1
    rw [ident, ranges.2] at stat
    convert stat using 1
    simp [rangeRows, rangeContent, toRow, List.map_map, Function.comp_def]

theorem full_implies_selected (full : Artifact) (tables : Tables)
    (h : RawConstraintsHold tables full.rawConstraints) :
    RawConstraintsHold tables (selectedRaw full) := by
  intro rule member
  obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
  apply h
  exact List.mem_map.mpr ⟨entry, (owned_coverage full entry).1 present |>.1, rfl⟩

def Accepts (full : Artifact) (a b q r : Scalar × Scalar × Scalar × Scalar) : Prop :=
  BoundSigned64.Accepts (selectedRaw full) a b q r

theorem component (full : Artifact) (h : check full = true)
    (a b : BitVec 64) (q r : Scalar × Scalar × Scalar × Scalar) :
    Accepts full (encodeFour a.toNat) (encodeFour b.toNat) q r ↔
      q = encodeFour (signedQuotient a b).toNat ∧
      r = encodeFour (signedRemainder a b).toNat :=
  BoundSigned64.component_iff _ (check_component full h) a b q r

/-- A full accepted trace supplies the helper guarantee at every active call tuple. -/
theorem full_sound (full : Artifact) (h : check full = true) (tables : Tables)
    (fixed : StaticHolds full tables) (accepted : RawConstraintsHold tables full.rawConstraints)
    (a b : BitVec 64) (q r : Scalar × Scalar × Scalar × Scalar)
    (active : fourList (encodeFour a.toNat) ++ fourList (encodeFour b.toNat) ++
      fourList q ++ fourList r ∈ signed64Target.messages tables) :
    q = encodeFour (signedQuotient a b).toNat ∧ r = encodeFour (signedRemainder a b).toNat := by
  have checks := h
  simp only [check, Bool.and_eq_true] at checks
  apply (component full h a b q r).1
  exact ⟨tables, checked_ranges_fixed full checks.1.1.1.2 tables fixed,
    full_implies_selected full tables accepted, active⟩

/-- Final composition is conditional on the actual decoded full artifact and checked binding. -/
theorem decoded_component (bytes : List UInt8) (full : Artifact)
    (decoded : ArtifactWire.decode bytes = some full) (bound : check full = true)
    (a b : BitVec 64) (q r : Scalar × Scalar × Scalar × Scalar) :
    ArtifactWire.Encodes bytes full ∧
    (Accepts full (encodeFour a.toNat) (encodeFour b.toNat) q r ↔
      q = encodeFour (signedQuotient a b).toNat ∧
      r = encodeFour (signedRemainder a b).toNat) :=
  ⟨(ArtifactWire.decode_iff bytes full).1 decoded, component full bound a b q r⟩

end DivRemFV.ArtifactBinding
