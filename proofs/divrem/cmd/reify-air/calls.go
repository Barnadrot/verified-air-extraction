package main

import (
	"fmt"
	"os"
	"strings"

	"divremfv/internal/airdata"
)

func writeCalls(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.Generated.Artifact\nimport DivRemFV.Calls\n\nnamespace DivRemFV.Generated\n\n")
	for _, c := range a.Constraints {
		if c.Kind != "lookup" || len(c.Sources) != 1 || len(c.Targets) != 1 {
			continue
		}
		source, target := c.Sources[0], c.Targets[0]
		module, ok := a.Module(target.Module)
		if !ok || module.Static {
			continue
		}
		if source.Selector == nil || target.Selector == nil {
			panic("dynamic call without selector")
		}
		bindings := []string{}
		sources := []string{}
		targets := []string{}
		for i, col := range source.Columns {
			s := fmt.Sprintf("readCell tables %d %d row", source.Module, col)
			t := fmt.Sprintf("readCell tables %d %d callee", target.Module, target.Columns[i])
			sources = append(sources, s)
			targets = append(targets, t)
			bindings = append(bindings, t+" = "+s)
		}
		fmt.Fprintf(&out, "theorem call%d (tables : Tables) (row : Nat)\n    (inside : row < (tables %d).size) (accepted : ConstraintsHold tables constraints)\n    (active : readCell tables %d %d row ≠ 0) :\n    ∃ callee, callee < (tables %d).size ∧ readCell tables %d %d callee ≠ 0 ∧\n      %s := by\n", c.ID, source.Module, source.Module, *source.Selector, target.Module, target.Module, *target.Selector, strings.Join(bindings, " ∧\n      "))
		fmt.Fprintf(&out, "  have found := lookup_call tables %s %s row inside\n    (by simpa [Port.Active] using active)\n    (by simpa only [c%d] using accepted c%d member%d)\n  obtain ⟨callee, inCallee, selected, tuple⟩ := found\n  refine ⟨callee, inCallee, ?_, ?_⟩\n  · simpa [Port.Active] using selected\n  · change [%s] = [%s] at tuple\n    simpa only [List.cons.injEq, and_true] using tuple\n\n", strings.TrimSuffix(strings.TrimPrefix(vectors([]airdata.Vector{source}), "["), "]"), strings.TrimSuffix(strings.TrimPrefix(vectors([]airdata.Vector{target}), "["), "]"), c.ID, c.ID, c.ID, strings.Join(targets, ", "), strings.Join(sources, ", "))
	}
	out.WriteString("end DivRemFV.Generated\n")
	check(os.WriteFile("DivRemFV/Generated/Calls.lean", []byte(out.String()), 0644))
}
