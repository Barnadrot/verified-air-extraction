import DivRemFV.SignedInterface64
import DivRemFV.ArtifactBinding

namespace DivRemFV.ComponentBoundary64
open NativeImport ArtifactBinding Generated

def Accepts (full : ArtifactWire.Artifact) (a b q r : Limbs64) : Prop :=
  ∃ tables : Tables, StaticRanges tables ∧ RawConstraintsHold tables (selectedRaw full) ∧
    fourList a ++ fourList b ++ fourList q ++ fourList r ∈ signed64Target.messages tables

theorem raw_component (full : ArtifactWire.Artifact) (checked : check full = true)
    (a b q r : Limbs64) : Accepts full a b q r ↔ Signed64Result a b q r := by
  rw [← signed64_raw_component_iff]
  constructor
  · rintro ⟨tables,ranges,accepted,member⟩
    exact ⟨tables,ranges,(Binding.check_sound _ _ (check_component full checked) tables).1 accepted,member⟩
  · rintro ⟨tables,ranges,accepted,member⟩
    exact ⟨tables,ranges,(Binding.check_sound _ _ (check_component full checked) tables).2 accepted,member⟩

theorem selected_holds (full : ArtifactWire.Artifact) (checked : check full = true)
    (tables : Tables) (accepted : RawConstraintsHold tables full.rawConstraints) :
    ConstraintsHold tables constraints :=
  (Binding.check_sound _ _ (check_component full checked) tables).1
    (full_implies_selected full tables accepted)

theorem incoming_holds (full : ArtifactWire.Artifact) (checked : check full = true)
    (tables : Tables) (accepted : RawConstraintsHold tables full.rawConstraints) :
    ConstraintsHold tables incomingConstraints := by
  apply (Binding.check_sound _ _ (check_interfaces full checked) tables).1
  intro rule member
  obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
  exact accepted _ (List.mem_map.mpr ⟨entry,(List.mem_filter.mp present).1,rfl⟩)

private def callerPort (selector : Nat) : Port :=
  ⟨41,some selector,#[32,33,34,35,36,37,38,39,55,56,57,58]⟩

private theorem call_message (tables : Tables) (selector : Nat) (target : Port) (row : Nat)
    (inside : row < (tables 41).size) (active : readCell tables 41 selector row ≠ 0)
    (lookup : (Constraint.lookup [callerPort selector] [target]).Holds tables) :
    fourList (readFour tables 41 32 row) ++ fourList (readFour tables 41 36 row) ++
      fourList (readFour tables 41 55 row) ∈ target.messages tables := by
  obtain ⟨callee,inCallee,selected,bindings⟩ := lookup_call tables (callerPort selector) target row
    inside ((return_active tables 41 selector _ row).2 active) lookup
  apply (Port.member_iff tables target _).2
  refine ⟨callee,inCallee,selected,?_⟩
  simpa [callerPort,Port.tuple,readFour,fourList] using bindings

/-- This is the actual DIV lookup result, before register writeback. -/
theorem div_call_sound (full : ArtifactWire.Artifact) (checked : check full = true)
    (tables : Tables) (ranges : StaticRanges tables)
    (accepted : RawConstraintsHold tables full.rawConstraints) (row : Nat)
    (inside : row < (tables 41).size) (active : readCell tables 41 131 row ≠ 0) :
    let a := readFour tables 41 32 row
    let b := readFour tables 41 36 row
    a = encodeFour (decodeFour a).toNat ∧ b = encodeFour (decodeFour b).toNat ∧
    readFour tables 41 55 row = encodeFour (signedQuotient (decodeFour a) (decodeFour b)).toNat := by
  have lookup := incoming_holds full checked tables accepted incoming9618
    (by simp [incomingConstraints])
  exact signed64_div_port_sound tables (selected_holds full checked tables accepted) ranges _ _ _
    (call_message tables 131 (callTarget incoming9618) row inside active lookup)

/-- This is the actual REM lookup result, before register writeback. -/
theorem rem_call_sound (full : ArtifactWire.Artifact) (checked : check full = true)
    (tables : Tables) (ranges : StaticRanges tables)
    (accepted : RawConstraintsHold tables full.rawConstraints) (row : Nat)
    (inside : row < (tables 41).size) (active : readCell tables 41 133 row ≠ 0) :
    let a := readFour tables 41 32 row
    let b := readFour tables 41 36 row
    a = encodeFour (decodeFour a).toNat ∧ b = encodeFour (decodeFour b).toNat ∧
    readFour tables 41 55 row = encodeFour (signedRemainder (decodeFour a) (decodeFour b)).toNat := by
  have lookup := incoming_holds full checked tables accepted incoming9622
    (by simp [incomingConstraints])
  exact signed64_rem_port_sound tables (selected_holds full checked tables accepted) ranges _ _ _
    (call_message tables 133 (callTarget incoming9622) row inside active lookup)

end DivRemFV.ComponentBoundary64
