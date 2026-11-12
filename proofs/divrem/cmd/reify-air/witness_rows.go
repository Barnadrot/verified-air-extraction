package main

import (
	"divremfv/internal/airdata"
	"fmt"
	"os"
	"strings"
)

func writeWitnessRows(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.WitnessTrace\n\nnamespace DivRemFV.Generated\n\n")
	for _, m := range a.Modules {
		if m.Static {
			continue
		}
		calls := []airdata.Constraint{}
		for _, c := range a.Constraints {
			if c.Owner == m.ID && c.Kind == "lookup" {
				target, _ := a.Module(c.Targets[0].Module)
				if !target.Static {
					calls = append(calls, c)
				}
			}
		}
		id := m.ID
		fmt.Fprintf(&out, "theorem witness_rows%d_complete (rows : Nat → Array NatRow)\n    (bounds : ∀ row, (inside : row < (rows %d).size) → Bounds%d (rows %d)[row].values)\n    (equations : ∀ row, (inside : row < (rows %d).size) → Equations%d (fun col => ((rows %d)[row].values col : K)))\n", id, id, id, id, id, id, id)
		for _, c := range calls {
			fmt.Fprintf(&out, "    (call%d : c%d.Holds (witnessTables rows))\n", c.ID, c.ID)
		}
		fmt.Fprintf(&out, "    : ConstraintsHold (witnessTables rows) module%dConstraints := by\n  apply rows%d_complete _ (witnessTables_fixed rows)\n  · intro row inside\n    have present : row < (rows %d).size := by simpa [witnessTables] using inside\n    apply bounds%d_of_le _ _ (bounds row present)\n    intro col\n    exact witnessTables_read_le rows %d row col (by decide) present\n  · intro row inside\n    have present : row < (rows %d).size := by simpa [witnessTables] using inside\n    have equal := funext (witnessTables_read_field rows %d row · (by decide) present)\n    change Equations%d (fun col => ((readCell (witnessTables rows) %d col row).val : K))\n    rw [equal]\n    exact equations row present\n", id, id, id, id, id, id, id, id, id)
		for _, c := range calls {
			fmt.Fprintf(&out, "  · exact call%d\n", c.ID)
		}
		out.WriteString("\n")
	}
	out.WriteString("end DivRemFV.Generated\n")
	check(os.WriteFile("DivRemFV/Generated/WitnessRows.lean", []byte(out.String()), 0644))
}
