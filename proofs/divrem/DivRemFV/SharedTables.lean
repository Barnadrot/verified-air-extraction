import DivRemFV.RowConstruction

namespace DivRemFV

def fixedRangeTables : Tables := fun mid =>
  match mid with
  | 84 => rangeRows 2
  | 85 => rangeRows 3
  | 86 => rangeRows 4
  | 90 => rangeRows 8
  | 94 => rangeRows 12
  | 95 => rangeRows 13
  | 96 => rangeRows 14
  | 97 => rangeRows 15
  | 98 => rangeRows 16
  | _ => #[]

theorem fixedRangeTables_fixed : StaticTablesFixed fixedRangeTables := by
  intro mid bits member
  simp only [rangeTablePairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl

def oneRowTables (mid width : Nat) (values : Nat → Nat) : Tables := fun current =>
  if current = mid then #[rowOfNat values width] else fixedRangeTables current

theorem oneRowTables_fixed (mid width : Nat) (values : Nat → Nat)
    (dynamic : ∀ bits, (mid,bits) ∉ rangeTablePairs) :
    StaticTablesFixed (oneRowTables mid width values) := by
  intro current bits member
  have other : current ≠ mid := by
    intro equal
    subst current
    exact dynamic bits member
  simpa only [oneRowTables, if_neg other] using fixedRangeTables_fixed current bits member

theorem oneRowTables_read (mid width col : Nat) (values : Nat → Nat) (inside : col < width) :
    readCell (oneRowTables mid width values) mid col 0 = scalarOfNat (values col) := by
  simpa only [readCell, oneRowTables, ↓reduceIte, Int.reduceLT, Int.toNat_zero,
    Array.getElem?_singleton, Option.getD_some] using rowOfNat_get values width col inside

theorem oneRowTables_read_nat (mid width col : Nat) (values : Nat → Nat)
    (outsideZero : ∀ col, width ≤ col → values col = 0) :
    (readCell (oneRowTables mid width values) mid col 0).val = values col % fieldModulus := by
  by_cases inside : col < width
  · rw [oneRowTables_read mid width col values inside]
    rfl
  · have outside := outsideZero col (by omega)
    simp [readCell, oneRowTables, rowOfNat, inside, outside]

theorem oneRowTables_read_field (mid width col : Nat) (values : Nat → Nat)
    (outsideZero : ∀ col, width ≤ col → values col = 0) :
    ((readCell (oneRowTables mid width values) mid col 0).val : K) = (values col : K) := by
  rw [oneRowTables_read_nat mid width col values outsideZero]
  simp

end DivRemFV
