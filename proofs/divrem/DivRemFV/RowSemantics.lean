import DivRemFV.FieldLifting
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

namespace DivRemFV

instance : Fact fieldModulus.Prime := ⟨by norm_num [fieldModulus]⟩

theorem scalar_zero_of_cast_zero {value : Scalar} (zero : (value.val : K) = 0) :
    value.val = 0 :=
  lift_field_equality value.val 0 value.isLt (by decide) (by simpa using zero)

theorem scalar_boolean_bound (value : Scalar)
    (equation : (value.val : K) * (value.val : K) - (value.val : K) = 0) :
    value.val < 2 := by
  have factored : (value.val : K) * ((value.val : K) - 1) = 0 := by
    simpa only [mul_sub, mul_one] using equation
  rcases mul_eq_zero.mp factored with zero | one
  · have := scalar_zero_of_cast_zero zero
    omega
  · have equal : (value.val : K) = (1 : K) := sub_eq_zero.mp one
    have := lift_field_equality value.val 1 value.isLt (by decide) equal
    omega

def rangeTablePairs : List (Nat × Nat) :=
  [(84, 2), (85, 3), (86, 4), (90, 8), (94, 12), (95, 13), (96, 14), (97, 15), (98, 16)]

def StaticRanges (tables : Tables) : Prop :=
  ∀ mid bits, (mid, bits) ∈ rangeTablePairs →
    ∀ row ∈ (tables mid).toList, (row[0]?.getD 0).val < 2 ^ bits

def rangeRows (bits : Nat) : Array Row :=
  ((List.range (2 ^ bits)).map fun value =>
    #[⟨value % fieldModulus, Nat.mod_lt _ (by decide)⟩]).toArray

def StaticTablesFixed (tables : Tables) : Prop :=
  ∀ mid bits, (mid, bits) ∈ rangeTablePairs → tables mid = rangeRows bits

theorem fixed_tables_have_ranges (tables : Tables) (fixed : StaticTablesFixed tables) :
    StaticRanges tables := by
  intro mid bits member row present
  rw [fixed mid bits member] at present
  simp only [rangeRows, List.toList_toArray, List.mem_map] at present
  obtain ⟨value, inside, rfl⟩ := present
  have bound := List.mem_range.mp inside
  change value % fieldModulus < 2 ^ bits
  exact lt_of_le_of_lt (Nat.mod_le _ _) bound

theorem single_column_member (tables : Tables) (mid col row : Nat)
    (inside : row < (tables mid).size) :
    [readCell tables mid col row] ∈ (Port.mk mid none #[col]).messages tables := by
  simp only [Port.messages, List.mem_filterMap]
  refine ⟨(tables mid)[row], ?_, ?_⟩
  · exact Array.getElem_mem_toList inside
  · simp [readCell, inside]

theorem lookup_range_bound (tables : Tables) (mid col target bits row : Nat)
    (inside : row < (tables mid).size)
    (lookup : (Constraint.lookup [⟨mid, none, #[col]⟩] [⟨target, none, #[0]⟩]).Holds tables)
    (bounded : ∀ entry ∈ (tables target).toList, (entry[0]?.getD 0).val < 2 ^ bits) :
    (readCell tables mid col row).val < 2 ^ bits := by
  have source := single_column_member tables mid col row inside
  have targetMember := lookup _ (by simpa [messages] using source)
  simp only [messages, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Port.messages, List.mem_filterMap] at targetMember
  obtain ⟨entry, member, equal⟩ := targetMember
  simp at equal
  have same := equal
  rw [← same]
  exact bounded entry member

end DivRemFV
