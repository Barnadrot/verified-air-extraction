package main

import (
	"divremfv/internal/airdata"
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

func instructionPart(full airdata.Artifact) airdata.Artifact {
	part := airdata.Artifact{Format: full.Format, Field: full.Field, Modulus: full.Modulus}
	for _, m := range full.Modules {
		if m.Name == "interpreter_c" || (m.Static && strings.HasPrefix(m.Name, "$range_u")) {
			part.Modules = append(part.Modules, m)
		}
	}
	root, ok := full.Module(41)
	if !ok || root.Name != "interpreter_c" {
		panic("interpreter identity changed")
	}
	for _, c := range full.Constraints {
		if c.Owner == root.ID {
			part.Constraints = append(part.Constraints, c)
		}
	}
	return part
}

func writeInstruction() {
	data, err := os.ReadFile("artifacts/air.json")
	check(err)
	var full airdata.Artifact
	check(json.Unmarshal(data, &full))
	part := instructionPart(full)
	data, err = json.MarshalIndent(part, "", "  ")
	check(err)
	check(os.WriteFile("artifacts/instruction-open-air.json", append(data, '\n'), 0644))
	old := reificationScope
	reificationScope = "Instruction"
	defer func() { reificationScope = old }()
	var ranges strings.Builder
	ranges.WriteString("import DivRemFV.RowSemantics\n\nnamespace DivRemFV.Instruction\n\ndef rangeTablePairs : List (Nat × Nat) := [")
	pairs := []string{}
	for _, m := range part.Modules {
		if m.Static {
			pairs = append(pairs, fmt.Sprintf("(%d,%d)", m.ID, *m.Columns[0].Bits))
		}
	}
	ranges.WriteString(strings.Join(pairs, ","))
	ranges.WriteString("]\n\ndef StaticRanges (tables : Tables) : Prop :=\n  ∀ mid bits,(mid,bits) ∈ rangeTablePairs →\n    ∀ row ∈ (tables mid).toList,(row[0]?.getD 0).val < 2^bits\n\ndef StaticTablesFixed (tables : Tables) : Prop :=\n  ∀ mid bits,(mid,bits) ∈ rangeTablePairs → tables mid = rangeRows bits\n\ntheorem fixed_tables_have_ranges (tables : Tables) (fixed : StaticTablesFixed tables) : StaticRanges tables := by\n  intro mid bits member row present\n  rw [fixed mid bits member] at present\n  simp only [rangeRows,List.toList_toArray,List.mem_map] at present\n  obtain ⟨value,inside,rfl⟩ := present\n  exact lt_of_le_of_lt (Nat.mod_le _ _) (List.mem_range.mp inside)\n\nend DivRemFV.Instruction\n")
	// Ranges itself imports the generic row semantics, not itself.
	check(os.MkdirAll("DivRemFV/Instruction", 0755))
	check(os.WriteFile("DivRemFV/Instruction/Ranges.lean", []byte(ranges.String()), 0644))
	writeArtifact(part)
	writeIntegerRows(part)
	writeConstruction(part)
	writeBoundsMap(part)
	writeReverseRows(part)
	writeNativeData(part)
}
