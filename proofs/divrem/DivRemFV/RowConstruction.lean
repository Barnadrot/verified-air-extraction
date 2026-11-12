import DivRemFV.Calls
import DivRemFV.RowSemantics

namespace DivRemFV

def scalarOfNat (value : Nat) : Scalar :=
  ⟨value % fieldModulus, Nat.mod_lt _ (by decide)⟩

def rowOfNat (values : Nat → Nat) (width : Nat) : Row :=
  Array.ofFn fun index : Fin width => scalarOfNat (values index)

theorem rowOfNat_get (values : Nat → Nat) (width col : Nat) (inside : col < width) :
    (rowOfNat values width)[col]?.getD 0 = scalarOfNat (values col) := by
  simp [rowOfNat, inside]

theorem row_bound_of_cells (tables : Tables) (mid col bound : Nat)
    (bounded : ∀ index, index < (tables mid).size → (readCell tables mid col index).val < bound) :
    ∀ row ∈ (tables mid).toList, (row[col]?.getD 0).val < bound := by
  intro row member
  obtain ⟨index, inside, equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
  rw [← equal]
  simpa only [readCell_inside tables mid col index inside] using bounded index inside

theorem range_value_member (bits : Nat) (value : Scalar)
    (bounded : value.val < 2 ^ bits) :
    [value] ∈ (Port.mk 0 none #[0]).messages (fun _ => rangeRows bits) := by
  simp only [Port.messages, rangeRows, List.toList_toArray, List.mem_filterMap]
  refine ⟨#[value], ?_, ?_⟩
  · simp only [List.mem_map]
    refine ⟨value.val, List.mem_range.mpr bounded, ?_⟩
    have canonical : value.val % fieldModulus = value.val := Nat.mod_eq_of_lt value.isLt
    simp only [canonical, Fin.eta]
  · simp

theorem lookup_range_complete (tables : Tables) (mid col target bits : Nat)
    (fixed : tables target = rangeRows bits)
    (bounded : ∀ row ∈ (tables mid).toList, (row[col]?.getD 0).val < 2 ^ bits) :
    (Constraint.lookup [⟨mid, none, #[col]⟩] [⟨target, none, #[0]⟩]).Holds tables := by
  intro message member
  simp only [messages, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Port.messages, List.mem_filterMap] at member ⊢
  obtain ⟨row, inside, equal⟩ := member
  simp at equal
  subst message
  refine ⟨#[(row[col]?.getD 0)], ?_, ?_⟩
  · rw [fixed]
    simp only [rangeRows, List.toList_toArray, List.mem_map]
    refine ⟨(row[col]?.getD 0).val, List.mem_range.mpr (bounded row inside), ?_⟩
    simp only [Nat.mod_eq_of_lt (row[col]?.getD 0).isLt, Fin.eta]
  · simp

theorem vanishing_complete (tables : Tables) (mid : Nat) (expr : Expr)
    (zero : ∀ row : Nat, row < (tables mid).size → expr.evalField tables mid row = 0) :
    (Constraint.vanishing mid none expr).Holds tables := by
  intro row _ inside
  have bound : row < (tables mid).size := by omega
  have equation := zero row bound
  have value : (expr.eval tables mid row : K) = 0 := by
    rw [Expr.eval_field_bridge]
    exact equation
  exact lift_field_equality _ 0 (expr.eval_canonical tables mid row) (by decide) (by simpa using value)

end DivRemFV
