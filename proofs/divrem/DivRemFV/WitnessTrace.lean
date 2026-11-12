import DivRemFV.SharedTables
import DivRemFV.Generated.BoundsMap
import DivRemFV.Generated.Construction

namespace DivRemFV
open Generated

structure NatRow where
  width : Nat
  values : Nat → Nat
  outside : ∀ col,width ≤ col → values col = 0

def NatRow.encode (row : NatRow) : Row := rowOfNat row.values row.width

theorem NatRow.encode_get (row : NatRow) (col : Nat) :
    row.encode[col]?.getD 0 = scalarOfNat (row.values col) := by
  by_cases inside : col < row.width
  · exact rowOfNat_get _ _ _ inside
  · have outside := row.outside col (by omega)
    simp [NatRow.encode,rowOfNat,inside,outside,scalarOfNat]

def witnessTables (rows : Nat → Array NatRow) : Tables := fun mid =>
  if mid ∈ [55,56,61,62,63,64,65,66] then (rows mid).map NatRow.encode else fixedRangeTables mid

theorem witnessTables_fixed (rows : Nat → Array NatRow) : StaticTablesFixed (witnessTables rows) := by
  intro mid bits member
  have outside : mid ∉ [55,56,61,62,63,64,65,66] := by
    simp only [rangeTablePairs,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
      ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  simpa only [witnessTables,if_neg outside] using fixedRangeTables_fixed mid bits member

theorem witnessTables_size (rows : Nat → Array NatRow) (mid : Nat)
    (dynamic : mid ∈ [55,56,61,62,63,64,65,66]) :
    ((witnessTables rows) mid).size = (rows mid).size := by
  simp only [witnessTables,if_pos dynamic,Array.size_map]

theorem witnessTables_read (rows : Nat → Array NatRow) (mid row col : Nat)
    (dynamic : mid ∈ [55,56,61,62,63,64,65,66]) (inside : row < (rows mid).size) :
    readCell (witnessTables rows) mid col row = scalarOfNat ((rows mid)[row].values col) := by
  have present : row < (witnessTables rows mid).size := by rwa [witnessTables_size _ _ dynamic]
  rw [readCell_inside _ _ _ _ present]
  simp only [witnessTables,if_pos dynamic,Array.getElem_map]
  exact NatRow.encode_get _ _

theorem witnessTables_read_le (rows : Nat → Array NatRow) (mid row col : Nat)
    (dynamic : mid ∈ [55,56,61,62,63,64,65,66]) (inside : row < (rows mid).size) :
    (readCell (witnessTables rows) mid col row).val ≤ (rows mid)[row].values col := by
  rw [witnessTables_read rows mid row col dynamic inside]
  exact Nat.mod_le _ _

theorem witnessTables_read_field (rows : Nat → Array NatRow) (mid row col : Nat)
    (dynamic : mid ∈ [55,56,61,62,63,64,65,66]) (inside : row < (rows mid).size) :
    ((readCell (witnessTables rows) mid col row).val : K) = ((rows mid)[row].values col : K) := by
  rw [witnessTables_read rows mid row col dynamic inside]
  simp [scalarOfNat]

theorem lookup_rows_complete (tables : Tables) (source target : Port)
    (matching : ∀ row,row < (tables source.moduleId).size → source.Active tables row →
      ∃ other,other < (tables target.moduleId).size ∧ target.Active tables other ∧
        target.tuple tables other = source.tuple tables row) :
    (Constraint.lookup [source] [target]).Holds tables := by
  intro message member
  simp only [messages,List.flatMap_cons,List.flatMap_nil,List.append_nil] at member ⊢
  obtain ⟨row,inside,active,equal⟩ := (Port.member_iff tables source message).1 member
  obtain ⟨other,present,selected,tuple⟩ := matching row inside active
  exact (Port.member_iff tables target message).2 ⟨other,present,selected,tuple.trans equal⟩

end DivRemFV
