import DivRemFV.WitnessTrace

namespace DivRemFV.Generated

theorem witness_rows55_complete (rows : Nat → Array NatRow)
    (bounds : ∀ row, (inside : row < (rows 55).size) → Bounds55 (rows 55)[row].values)
    (equations : ∀ row, (inside : row < (rows 55).size) → Equations55 (fun col => ((rows 55)[row].values col : K)))
    : ConstraintsHold (witnessTables rows) module55Constraints := by
  apply rows55_complete _ (witnessTables_fixed rows)
  · intro row inside
    have present : row < (rows 55).size := by simpa [witnessTables] using inside
    apply bounds55_of_le _ _ (bounds row present)
    intro col
    exact witnessTables_read_le rows 55 row col (by decide) present
  · intro row inside
    have present : row < (rows 55).size := by simpa [witnessTables] using inside
    have equal := funext (witnessTables_read_field rows 55 row · (by decide) present)
    change Equations55 (fun col => ((readCell (witnessTables rows) 55 col row).val : K))
    rw [equal]
    exact equations row present

theorem witness_rows56_complete (rows : Nat → Array NatRow)
    (bounds : ∀ row, (inside : row < (rows 56).size) → Bounds56 (rows 56)[row].values)
    (equations : ∀ row, (inside : row < (rows 56).size) → Equations56 (fun col => ((rows 56)[row].values col : K)))
    : ConstraintsHold (witnessTables rows) module56Constraints := by
  apply rows56_complete _ (witnessTables_fixed rows)
  · intro row inside
    have present : row < (rows 56).size := by simpa [witnessTables] using inside
    apply bounds56_of_le _ _ (bounds row present)
    intro col
    exact witnessTables_read_le rows 56 row col (by decide) present
  · intro row inside
    have present : row < (rows 56).size := by simpa [witnessTables] using inside
    have equal := funext (witnessTables_read_field rows 56 row · (by decide) present)
    change Equations56 (fun col => ((readCell (witnessTables rows) 56 col row).val : K))
    rw [equal]
    exact equations row present

theorem witness_rows61_complete (rows : Nat → Array NatRow)
    (bounds : ∀ row, (inside : row < (rows 61).size) → Bounds61 (rows 61)[row].values)
    (equations : ∀ row, (inside : row < (rows 61).size) → Equations61 (fun col => ((rows 61)[row].values col : K)))
    : ConstraintsHold (witnessTables rows) module61Constraints := by
  apply rows61_complete _ (witnessTables_fixed rows)
  · intro row inside
    have present : row < (rows 61).size := by simpa [witnessTables] using inside
    apply bounds61_of_le _ _ (bounds row present)
    intro col
    exact witnessTables_read_le rows 61 row col (by decide) present
  · intro row inside
    have present : row < (rows 61).size := by simpa [witnessTables] using inside
    have equal := funext (witnessTables_read_field rows 61 row · (by decide) present)
    change Equations61 (fun col => ((readCell (witnessTables rows) 61 col row).val : K))
    rw [equal]
    exact equations row present

theorem witness_rows62_complete (rows : Nat → Array NatRow)
    (bounds : ∀ row, (inside : row < (rows 62).size) → Bounds62 (rows 62)[row].values)
    (equations : ∀ row, (inside : row < (rows 62).size) → Equations62 (fun col => ((rows 62)[row].values col : K)))
    (call11984 : c11984.Holds (witnessTables rows))
    (call11985 : c11985.Holds (witnessTables rows))
    (call11986 : c11986.Holds (witnessTables rows))
    (call11989 : c11989.Holds (witnessTables rows))
    (call11991 : c11991.Holds (witnessTables rows))
    : ConstraintsHold (witnessTables rows) module62Constraints := by
  apply rows62_complete _ (witnessTables_fixed rows)
  · intro row inside
    have present : row < (rows 62).size := by simpa [witnessTables] using inside
    apply bounds62_of_le _ _ (bounds row present)
    intro col
    exact witnessTables_read_le rows 62 row col (by decide) present
  · intro row inside
    have present : row < (rows 62).size := by simpa [witnessTables] using inside
    have equal := funext (witnessTables_read_field rows 62 row · (by decide) present)
    change Equations62 (fun col => ((readCell (witnessTables rows) 62 col row).val : K))
    rw [equal]
    exact equations row present
  · exact call11984
  · exact call11985
  · exact call11986
  · exact call11989
  · exact call11991

theorem witness_rows63_complete (rows : Nat → Array NatRow)
    (bounds : ∀ row, (inside : row < (rows 63).size) → Bounds63 (rows 63)[row].values)
    (equations : ∀ row, (inside : row < (rows 63).size) → Equations63 (fun col => ((rows 63)[row].values col : K)))
    : ConstraintsHold (witnessTables rows) module63Constraints := by
  apply rows63_complete _ (witnessTables_fixed rows)
  · intro row inside
    have present : row < (rows 63).size := by simpa [witnessTables] using inside
    apply bounds63_of_le _ _ (bounds row present)
    intro col
    exact witnessTables_read_le rows 63 row col (by decide) present
  · intro row inside
    have present : row < (rows 63).size := by simpa [witnessTables] using inside
    have equal := funext (witnessTables_read_field rows 63 row · (by decide) present)
    change Equations63 (fun col => ((readCell (witnessTables rows) 63 col row).val : K))
    rw [equal]
    exact equations row present

theorem witness_rows64_complete (rows : Nat → Array NatRow)
    (bounds : ∀ row, (inside : row < (rows 64).size) → Bounds64 (rows 64)[row].values)
    (equations : ∀ row, (inside : row < (rows 64).size) → Equations64 (fun col => ((rows 64)[row].values col : K)))
    (call12114 : c12114.Holds (witnessTables rows))
    (call12115 : c12115.Holds (witnessTables rows))
    (call12116 : c12116.Holds (witnessTables rows))
    (call12119 : c12119.Holds (witnessTables rows))
    (call12121 : c12121.Holds (witnessTables rows))
    : ConstraintsHold (witnessTables rows) module64Constraints := by
  apply rows64_complete _ (witnessTables_fixed rows)
  · intro row inside
    have present : row < (rows 64).size := by simpa [witnessTables] using inside
    apply bounds64_of_le _ _ (bounds row present)
    intro col
    exact witnessTables_read_le rows 64 row col (by decide) present
  · intro row inside
    have present : row < (rows 64).size := by simpa [witnessTables] using inside
    have equal := funext (witnessTables_read_field rows 64 row · (by decide) present)
    change Equations64 (fun col => ((readCell (witnessTables rows) 64 col row).val : K))
    rw [equal]
    exact equations row present
  · exact call12114
  · exact call12115
  · exact call12116
  · exact call12119
  · exact call12121

theorem witness_rows65_complete (rows : Nat → Array NatRow)
    (bounds : ∀ row, (inside : row < (rows 65).size) → Bounds65 (rows 65)[row].values)
    (equations : ∀ row, (inside : row < (rows 65).size) → Equations65 (fun col => ((rows 65)[row].values col : K)))
    : ConstraintsHold (witnessTables rows) module65Constraints := by
  apply rows65_complete _ (witnessTables_fixed rows)
  · intro row inside
    have present : row < (rows 65).size := by simpa [witnessTables] using inside
    apply bounds65_of_le _ _ (bounds row present)
    intro col
    exact witnessTables_read_le rows 65 row col (by decide) present
  · intro row inside
    have present : row < (rows 65).size := by simpa [witnessTables] using inside
    have equal := funext (witnessTables_read_field rows 65 row · (by decide) present)
    change Equations65 (fun col => ((readCell (witnessTables rows) 65 col row).val : K))
    rw [equal]
    exact equations row present

theorem witness_rows66_complete (rows : Nat → Array NatRow)
    (bounds : ∀ row, (inside : row < (rows 66).size) → Bounds66 (rows 66)[row].values)
    (equations : ∀ row, (inside : row < (rows 66).size) → Equations66 (fun col => ((rows 66)[row].values col : K)))
    : ConstraintsHold (witnessTables rows) module66Constraints := by
  apply rows66_complete _ (witnessTables_fixed rows)
  · intro row inside
    have present : row < (rows 66).size := by simpa [witnessTables] using inside
    apply bounds66_of_le _ _ (bounds row present)
    intro col
    exact witnessTables_read_le rows 66 row col (by decide) present
  · intro row inside
    have present : row < (rows 66).size := by simpa [witnessTables] using inside
    have equal := funext (witnessTables_read_field rows 66 row · (by decide) present)
    change Equations66 (fun col => ((readCell (witnessTables rows) 66 col row).val : K))
    rw [equal]
    exact equations row present

end DivRemFV.Generated
