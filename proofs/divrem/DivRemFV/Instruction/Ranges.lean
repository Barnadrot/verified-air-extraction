import DivRemFV.RowSemantics

namespace DivRemFV.Instruction

def rangeTablePairs : List (Nat × Nat) := [(84,2),(85,3),(86,4),(87,5),(88,6),(89,7),(90,8),(91,9),(92,10),(93,11),(94,12),(95,13),(96,14),(97,15),(98,16)]

def StaticRanges (tables : Tables) : Prop :=
  ∀ mid bits,(mid,bits) ∈ rangeTablePairs →
    ∀ row ∈ (tables mid).toList,(row[0]?.getD 0).val < 2^bits

def StaticTablesFixed (tables : Tables) : Prop :=
  ∀ mid bits,(mid,bits) ∈ rangeTablePairs → tables mid = rangeRows bits

theorem fixed_tables_have_ranges (tables : Tables) (fixed : StaticTablesFixed tables) : StaticRanges tables := by
  intro mid bits member row present
  rw [fixed mid bits member] at present
  simp only [rangeRows,List.toList_toArray,List.mem_map] at present
  obtain ⟨value,inside,rfl⟩ := present
  exact lt_of_le_of_lt (Nat.mod_le _ _) (List.mem_range.mp inside)

end DivRemFV.Instruction
