import DivRemFV.NativeImport

namespace DivRemFV.Binding

open NativeImport

def check (captured : List RawConstraint) (expected : List Constraint) : Bool :=
  decide (captured.map RawConstraint.translate = expected)

theorem check_sound (captured : List RawConstraint) (expected : List Constraint)
    (bound : check captured expected = true) (tables : Tables) :
    RawConstraintsHold tables captured ↔ ConstraintsHold tables expected := by
  have equal : captured.map RawConstraint.translate = expected := of_decide_eq_true bound
  rw [← equal]
  exact (translate_constraints_holds tables captured).symm

def subsetCheck (full selected : List Constraint) : Bool :=
  selected.all fun constraint => decide (constraint ∈ full)

theorem subsetCheck_sound (full selected : List Constraint)
    (bound : subsetCheck full selected = true) (tables : Tables)
    (accepted : ConstraintsHold tables full) : ConstraintsHold tables selected := by
  apply constraints_subset tables full selected _ accepted
  simpa only [subsetCheck, List.all_eq_true, decide_eq_true_eq] using bound

theorem captured_subset_sound (full : List RawConstraint) (selected : List Constraint)
    (bound : subsetCheck (full.map RawConstraint.translate) selected = true)
    (tables : Tables) (accepted : RawConstraintsHold tables full) :
    ConstraintsHold tables selected := by
  exact subsetCheck_sound _ selected bound tables
    ((translate_constraints_holds tables full).2 accepted)

end DivRemFV.Binding
