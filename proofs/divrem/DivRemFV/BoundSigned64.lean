import DivRemFV.Binding
import DivRemFV.SignedContract64

namespace DivRemFV.BoundSigned64

open NativeImport

def Accepts (captured : List RawConstraint)
    (a b q r : Scalar × Scalar × Scalar × Scalar) : Prop :=
  ∃ tables : Tables, StaticTablesFixed tables ∧ RawConstraintsHold tables captured ∧
    fourList a ++ fourList b ++ fourList q ++ fourList r ∈ signed64Target.messages tables

theorem accepts_iff (captured : List RawConstraint)
    (bound : Binding.check captured Generated.constraints = true)
    (a b q r : Scalar × Scalar × Scalar × Scalar) :
    Accepts captured a b q r ↔ signed64Accepts a b q r := by
  constructor
  · rintro ⟨tables, fixed, accepted, active⟩
    exact ⟨tables, fixed, (Binding.check_sound captured _ bound tables).1 accepted, active⟩
  · rintro ⟨tables, fixed, accepted, active⟩
    exact ⟨tables, fixed, (Binding.check_sound captured _ bound tables).2 accepted, active⟩

theorem component_iff (captured : List RawConstraint)
    (bound : Binding.check captured Generated.constraints = true)
    (a b : BitVec 64) (q r : Scalar × Scalar × Scalar × Scalar) :
    Accepts captured (encodeFour a.toNat) (encodeFour b.toNat) q r ↔
      q = encodeFour (signedQuotient a b).toNat ∧
      r = encodeFour (signedRemainder a b).toNat := by
  rw [accepts_iff captured bound]
  exact signed64_component_iff a b q r

end DivRemFV.BoundSigned64
