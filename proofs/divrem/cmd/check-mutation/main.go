package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"os"

	"divremfv/internal/airdata"
)

func main() {
	bits := flag.Int("bits", 64, "unsigned dependency width: 32 or 64")
	flag.Parse()
	if *bits != 32 && *bits != 64 {
		panic("unsupported width")
	}
	moduleName := fmt.Sprintf("divMod_%d_uu", *bits)
	data, err := os.ReadFile("artifacts/divrem-air.json")
	check(err)
	var a airdata.Artifact
	check(json.Unmarshal(data, &a))
	check(a.Validate())
	var module airdata.Module
	for _, m := range a.Modules {
		if m.Name == moduleName {
			module = m
			break
		}
	}
	if module.Name == "" {
		panic("unsigned module absent")
	}
	row := make([]uint64, len(module.Columns))
	values := map[string]uint64{
		"b'0": 2, "r'0": 1, "qy_plus_r$6'0": 1, "rw1$7'0": 2,
		"fsc$9": 1, "s$23": 2, "$ret": 1,
		"(inv (+ divMod_32_uu:b'1 divMod_32_uu:b'0))": 1065353217,
	}
	if *bits == 64 {
		values = map[string]uint64{
			"b'0": 2, "r'0": 1, "qy_plus_r$6'0": 1, "rw1$7'0": 2,
			"fsc$9": 1, "s$45": 2, "$ret": 1,
			"(inv (+ divMod_64_uu:b'3 divMod_64_uu:b'2 divMod_64_uu:b'1 divMod_64_uu:b'0))": 1065353217,
		}
	}
	for _, col := range module.Columns {
		row[col.ID] = values[col.Name]
		delete(values, col.Name)
	}
	if len(values) != 0 {
		panic("witness layout changed; review required")
	}
	failed := []uint{}
	checked := 0
	for _, c := range a.Constraints {
		if c.Owner != module.ID {
			continue
		}
		checked++
		switch c.Kind {
		case "vanishing":
			if c.Domain != nil || c.Expr.HasShift() {
				panic("unsupported row shape")
			}
			value, err := c.Expr.Eval([][]uint64{row}, 0)
			check(err)
			if value != 0 {
				failed = append(failed, c.ID)
			}
		case "lookup":
			if len(c.Sources) != 1 || len(c.Targets) != 1 {
				panic("unexpected lookup")
			}
			source, target := c.Sources[0], c.Targets[0]
			if source.Module != module.ID || source.Selector != nil || len(source.Columns) != 1 || target.Selector != nil || len(target.Columns) != 1 {
				panic("unexpected lookup shape")
			}
			fixed, ok := a.Module(target.Module)
			if !ok || !fixed.Static {
				panic("nonstatic range target")
			}
			value := row[source.Columns[0]]
			found := false
			for _, entry := range fixed.Content {
				if entry[target.Columns[0]] == value {
					found = true
					break
				}
			}
			if !found {
				failed = append(failed, c.ID)
			}
		default:
			panic("unsupported constraint")
		}
	}
	if len(failed) != 1 {
		panic(fmt.Sprintf("expected one necessary constraint; failures: %v", failed))
	}
	var removed airdata.Constraint
	for _, c := range a.Constraints {
		if c.ID == failed[0] {
			removed = c
			break
		}
	}
	if *bits == 32 && removed.Name != "inst#26" {
		panic("unexpected rejecting constraint")
	}
	if *bits == 64 && removed.Name != "inst#58" {
		panic("unexpected rejecting constraint")
	}
	result := map[string]any{
		"format": "divrem-checked-mutation-v1", "module": module.Name,
		"input_a": 0, "input_b": 2, "false_quotient": 0, "false_remainder": 1,
		"correct_quotient": 0, "correct_remainder": 0,
		"checked_constraints": checked, "removed_constraint_id": removed.ID,
		"removed_constraint_name": removed.Name, "witness_row": row,
		"original": "rejected", "mutant": "accepted by all remaining module constraints",
		"scope": "finite row counterexample checked against exported AIR; not a defect in the original constraints",
	}
	encoded, err := json.MarshalIndent(result, "", "  ")
	check(err)
	path := "artifacts/checked-mutation.json"
	if *bits == 64 {
		path = "artifacts/checked-mutation64.json"
	}
	check(os.WriteFile(path, append(encoded, '\n'), 0644))
	fmt.Printf("Original rejects false 0 / 2 witness. Deleting constraint %d admits it; checked %d module constraints.\n", removed.ID, checked)
}

func check(err error) {
	if err != nil {
		panic(err)
	}
}
