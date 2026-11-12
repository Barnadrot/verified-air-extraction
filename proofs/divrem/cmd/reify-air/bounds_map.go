package main

import (
	"divremfv/internal/airdata"
	"fmt"

	"strings"
)

func writeBoundsMap(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.Generated.Artifact\n\nnamespace DivRemFV.Generated\n\n")
	for _, m := range a.Modules {
		if m.Static {
			continue
		}
		fmt.Fprintf(&out, "theorem bounds%d_of_le (v w : Nat → Nat) (bounds : Bounds%d v)\n    (smaller : ∀ col, w col ≤ v col) : Bounds%d w := by\n  constructor\n", m.ID, m.ID, m.ID)
		for _, col := range m.Columns {
			if col.Bits != nil && findRange(a, m.ID, col) != nil {
				fmt.Fprintf(&out, "  · exact lt_of_le_of_lt (smaller %d) bounds.b%d\n", col.ID, col.ID)
			}
		}
		out.WriteString("\n")
	}
	out.WriteString("end DivRemFV.Generated\n")
	writeScoped("BoundsMap", out.String())
}
