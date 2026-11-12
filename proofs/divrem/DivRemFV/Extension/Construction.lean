import DivRemFV.Extension.Artifact
import DivRemFV.RowConstruction

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV.Extension

def module67Constraints : List Constraint := [c12204,c12205,c12206,c12207,c12208,c12209,c12210,c12211,c12212,c12213,c12214,c12215,c12216,c12217,c12218,c12219,c12220,c12221]

theorem rows67_complete (tables : Tables)
    (fixed : StaticTablesFixed tables)
    (bounds : ∀ row, row < (tables 67).size → Bounds67 (fun col => (readCell tables 67 col row).val))
    (equations : ∀ row, row < (tables 67).size → Equations67 (fun col => ((readCell tables 67 col row).val : K)))
    : ConstraintsHold tables module67Constraints := by
  intro constraint member
  simp only [module67Constraints, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · unfold c12204
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12204
    simpa only [Expr.evalField, Int.add_zero] using h
  · unfold c12205
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12205
    simpa only [Expr.evalField, Int.add_zero] using h
  · unfold c12206
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12206
    simpa only [Expr.evalField, Int.add_zero] using h
  · unfold c12207
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12207
    simpa only [Expr.evalField, Int.add_zero] using h
  · unfold c12208
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12208
    simpa only [Expr.evalField, Int.add_zero] using h
  · unfold c12209
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12209
    simpa only [Expr.evalField, Int.add_zero] using h
  · unfold c12210
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12210
    simpa only [Expr.evalField, Int.add_zero] using h
  · unfold c12211
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12211
    simpa only [Expr.evalField, Int.add_zero] using h
  · apply lookup_range_complete tables 67 0 98 16 (fixed 98 16 (by decide))
    apply row_bound_of_cells
    intro row inside
    exact (bounds row inside).b0
  · apply lookup_range_complete tables 67 1 98 16 (fixed 98 16 (by decide))
    apply row_bound_of_cells
    intro row inside
    exact (bounds row inside).b1
  · apply lookup_range_complete tables 67 2 98 16 (fixed 98 16 (by decide))
    apply row_bound_of_cells
    intro row inside
    exact (bounds row inside).b2
  · apply lookup_range_complete tables 67 3 98 16 (fixed 98 16 (by decide))
    apply row_bound_of_cells
    intro row inside
    exact (bounds row inside).b3
  · apply lookup_range_complete tables 67 4 98 16 (fixed 98 16 (by decide))
    apply row_bound_of_cells
    intro row inside
    exact (bounds row inside).b4
  · apply lookup_range_complete tables 67 5 98 16 (fixed 98 16 (by decide))
    apply row_bound_of_cells
    intro row inside
    exact (bounds row inside).b5
  · unfold c12218
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12218
    simpa only [Expr.evalField, Int.add_zero] using h
  · apply lookup_range_complete tables 67 7 97 15 (fixed 97 15 (by decide))
    apply row_bound_of_cells
    intro row inside
    exact (bounds row inside).b7
  · apply lookup_range_complete tables 67 8 98 16 (fixed 98 16 (by decide))
    apply row_bound_of_cells
    intro row inside
    exact (bounds row inside).b8
  · unfold c12221
    apply vanishing_complete
    intro row inside
    have h := (equations row inside).h12221
    simpa only [Expr.evalField, Int.add_zero] using h

theorem constraints_partition : constraints = module67Constraints := by rfl

theorem constraints_from_modules (tables : Tables)
    (h67 : ConstraintsHold tables module67Constraints)
    : ConstraintsHold tables constraints := by
  intro constraint member
  rw [constraints_partition] at member
  exact h67 constraint member

end DivRemFV.Extension
