import DivRemFV.RowSemantics

namespace DivRemFV

theorem readCell_inside (tables : Tables) (mid col row : Nat) (inside : row < (tables mid).size) :
    readCell tables mid col row = ((tables mid)[row])[col]?.getD 0 := by
  simp [readCell, inside]

def Port.Active (tables : Tables) (port : Port) (row : Nat) : Prop :=
  port.selector.all (fun col => readCell tables port.moduleId col row != 0) = true

def Port.tuple (tables : Tables) (port : Port) (row : Nat) : List Scalar :=
  port.columns.toList.map fun col => readCell tables port.moduleId col row

theorem Port.member_iff (tables : Tables) (port : Port) (message : List Scalar) :
    message ∈ port.messages tables ↔
    ∃ row, row < (tables port.moduleId).size ∧ port.Active tables row ∧
      port.tuple tables row = message := by
  simp only [Port.messages, List.mem_filterMap]
  constructor
  · rintro ⟨entry, present, selected⟩
    have arrayMember : entry ∈ tables port.moduleId := Array.mem_toList_iff.mp present
    obtain ⟨row, inside, equal⟩ := Array.mem_iff_getElem.mp arrayMember
    rw [← equal] at selected
    split at selected
    next active =>
      refine ⟨row, inside, ?_, ?_⟩
      · simpa only [Port.Active, readCell_inside tables _ _ _ inside] using active
      · simpa only [Port.tuple, readCell_inside tables _ _ _ inside, Option.some.injEq] using selected
    next => simp at selected
  · rintro ⟨row, inside, active, tuple⟩
    refine ⟨(tables port.moduleId)[row], Array.getElem_mem_toList inside, ?_⟩
    have selected : port.selector.all (fun col => ((tables port.moduleId)[row])[col]?.getD 0 != 0) = true := by
      simpa only [Port.Active, readCell_inside tables _ _ _ inside] using active
    simp only [selected, ↓reduceIte, Option.some.injEq]
    simpa only [Port.tuple, readCell_inside tables _ _ _ inside] using tuple

theorem lookup_call (tables : Tables) (source target : Port) (sourceRow : Nat)
    (inside : sourceRow < (tables source.moduleId).size) (active : source.Active tables sourceRow)
    (accepted : (Constraint.lookup [source] [target]).Holds tables) :
    ∃ targetRow, targetRow < (tables target.moduleId).size ∧ target.Active tables targetRow ∧
      target.tuple tables targetRow = source.tuple tables sourceRow := by
  have sent := (Port.member_iff tables source _).2 ⟨sourceRow, inside, active, rfl⟩
  have received := accepted _ (by simpa only [messages, List.flatMap_cons, List.flatMap_nil,
    List.append_nil] using sent)
  apply (Port.member_iff tables target _).1
  simpa only [messages, List.flatMap_cons, List.flatMap_nil, List.append_nil] using received

theorem return_active (tables : Tables) (mid ret : Nat) (columns : Array Nat) (row : Nat) :
    (Port.mk mid (some ret) columns).Active tables row ↔ readCell tables mid ret row ≠ 0 := by
  simp [Port.Active]

end DivRemFV
