package main

import (
	"divremfv/internal/airdata"
	"fmt"

	"strings"
)

func writeConstruction(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.Generated.Artifact\nimport DivRemFV.RowConstruction\n\nset_option maxRecDepth 4096\nset_option maxHeartbeats 2000000\n\nnamespace DivRemFV.Generated\n\n")
	mids := []uint{}
	for _, m := range a.Modules {
		if m.Static {
			continue
		}
		mids = append(mids, m.ID)
		cs := []airdata.Constraint{}
		calls := []airdata.Constraint{}
		for _, c := range a.Constraints {
			if c.Owner != m.ID {
				continue
			}
			cs = append(cs, c)
			if c.Kind == "lookup" {
				target, ok := a.Module(c.Targets[0].Module)
				if !ok && reificationScope != "Instruction" {
					panic("missing target")
				}
				if !target.Static {
					calls = append(calls, c)
				}
			}
		}
		fmt.Fprintf(&out, "def module%dConstraints : List Constraint := [", m.ID)
		for i, c := range cs {
			if i > 0 {
				out.WriteString(",")
			}
			fmt.Fprintf(&out, "c%d", c.ID)
		}
		out.WriteString("]\n\n")
		fmt.Fprintf(&out, "theorem rows%d_complete (tables : Tables)\n    (fixed : StaticTablesFixed tables)\n    (bounds : ∀ row, row < (tables %d).size → Bounds%d (fun col => (readCell tables %d col row).val))\n    (equations : ∀ row, row < (tables %d).size → Equations%d (fun col => ((readCell tables %d col row).val : K)))\n", m.ID, m.ID, m.ID, m.ID, m.ID, m.ID, m.ID)
		for _, c := range calls {
			fmt.Fprintf(&out, "    (call%d : c%d.Holds tables)\n", c.ID, c.ID)
		}
		fmt.Fprintf(&out, "    : ConstraintsHold tables module%dConstraints := by\n  intro constraint member\n  simp only [module%dConstraints, List.mem_cons, List.not_mem_nil, or_false] at member\n  rcases member with ", m.ID, m.ID)
		for i := range cs {
			if i > 0 {
				out.WriteString(" | ")
			}
			out.WriteString("rfl")
		}
		out.WriteString("\n")
		for _, c := range cs {
			switch c.Kind {
			case "vanishing":
				if c.Domain != nil || c.Expr.HasShift() {
					panic("row construction requires atomic helpers")
				}
				fmt.Fprintf(&out, "  · unfold c%d\n    apply vanishing_complete\n    intro row inside\n    have h := (equations row inside).h%d\n    simpa only [Expr.evalField, Int.add_zero] using h\n", c.ID, c.ID)
			case "lookup":
				if len(c.Sources) != 1 || len(c.Targets) != 1 {
					panic("unsupported lookup")
				}
				target, _ := a.Module(c.Targets[0].Module)
				if !target.Static {
					fmt.Fprintf(&out, "  · exact call%d\n", c.ID)
					continue
				}
				s, t := c.Sources[0], c.Targets[0]
				if s.Selector != nil || t.Selector != nil || len(s.Columns) != 1 || len(t.Columns) != 1 || t.Columns[0] != 0 {
					panic("unsupported range lookup")
				}
				bits := *target.Columns[0].Bits
				// Static target metadata is checked independently against rangeTablePairs by Lean.
				fmt.Fprintf(&out, "  · apply lookup_range_complete tables %d %d %d %d (fixed %d %d (by decide))\n    apply row_bound_of_cells\n    intro row inside\n    exact (bounds row inside).b%d\n", m.ID, s.Columns[0], t.Module, bits, t.Module, bits, s.Columns[0])
			default:
				panic("unsupported row constraint")
			}
		}
		out.WriteString("\n")
	}
	out.WriteString("theorem constraints_partition : constraints = ")
	for i, mid := range mids {
		if i > 0 {
			out.WriteString(" ++ ")
		}
		fmt.Fprintf(&out, "module%dConstraints", mid)
	}
	out.WriteString(" := by rfl\n\n")
	out.WriteString("theorem constraints_from_modules (tables : Tables)\n")
	for _, mid := range mids {
		fmt.Fprintf(&out, "    (h%d : ConstraintsHold tables module%dConstraints)\n", mid, mid)
	}
	out.WriteString("    : ConstraintsHold tables constraints := by\n  intro constraint member\n  rw [constraints_partition] at member\n")
	if len(mids) == 1 {
		fmt.Fprintf(&out, "  exact h%d constraint member\n", mids[0])
	} else {
		out.WriteString("  simp only [List.mem_append, or_assoc] at member\n  rcases member with ")
		for i, mid := range mids {
			if i > 0 {
				out.WriteString(" | ")
			}
			fmt.Fprintf(&out, "m%d", mid)
		}
		out.WriteString("\n")
		for _, mid := range mids {
			fmt.Fprintf(&out, "  · exact h%d constraint m%d\n", mid, mid)
		}
	}
	out.WriteString("\nend DivRemFV.Generated\n")
	writeScoped("Construction", out.String())
}
