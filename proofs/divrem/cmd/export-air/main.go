package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"os"
	"runtime/debug"
	"time"

	"divremfv/internal/airdata"

	"github.com/LFDT-Lineth/lineth-monorepo/arithmetization/gopkg/embedded"
	"github.com/LFDT-Lineth/zkc/pkg/zkc/constraints"
)

func main() {
	out := flag.String("out", "artifacts/air-inventory.json", "inventory output")
	flag.Parse()
	started := time.Now()
	buildInfo, ok := debug.ReadBuildInfo()
	if !ok {
		panic("Go build information absent")
	}
	bin, err := embedded.CompiledBinaryFile()
	if err != nil {
		panic(err)
	}
	if bin.Field().Name != "KOALABEAR_16" || bin.Field().Modulus().Uint64() != airdata.Modulus {
		panic("unsupported source compilation field")
	}
	s := bin.AirConstraints()
	validationErrors := []string{}
	for _, err := range constraints.Validate(s) {
		validationErrors = append(validationErrors, err.Error())
	}
	modules := []map[string]any{}
	for id, m := range s.Modules().Collect() {
		columns := []map[string]any{}
		for rid, r := range m.Registers() {
			var bits any
			if !r.IsNative() {
				bits = r.Width()
			}
			columns = append(columns, map[string]any{
				"id": rid, "name": r.Name(), "bits": bits,
				"input": r.IsInput(), "output": r.IsOutput(), "native": r.IsNative(),
			})
		}
		constraints := []string{}
		for _, c := range m.Constraints().Collect() {
			constraints = append(constraints, c.Lisp(s).String(false))
		}
		modules = append(modules, map[string]any{
			"id": id, "name": m.Name(), "static": m.IsStatic(), "native": m.IsNative(),
			"columns": columns, "constraints": constraints,
		})
	}
	data, err := json.MarshalIndent(map[string]any{
		"format": "divrem-air-inventory-v1", "field": bin.Field().Name,
		"modulus": bin.Field().Modulus().String(), "modules": modules,
		"constraint_count":                len(s.Constraints().Collect()),
		"structural_validation_errors":    validationErrors,
		"research_baseline_lineth_commit": "2737d8c6b0cdba2b54c195aa6c10958538c5f3e4",
		"go_build_info":                   buildInfo,
		"claim":                           "inventory only; no component or production proof",
	}, "", "  ")
	if err != nil {
		panic(err)
	}
	if err := os.WriteFile(*out, append(data, '\n'), 0o644); err != nil {
		panic(err)
	}
	artifact, err := airdata.Export(s)
	if err != nil {
		panic(err)
	}
	roots := []string{"divMod_64_uu", "divMod_64_ss", "divMod_32_uu", "divMod_32_ss"}
	slice, boundaries, selected, err := artifact.Slice(roots)
	if err != nil {
		panic(err)
	}
	writeJSON("artifacts/air.json", artifact)
	wire, err := airdata.EncodeArtifactWire(artifact)
	if err != nil {
		panic(err)
	}
	if err := os.WriteFile("artifacts/air.wire", wire, 0o644); err != nil {
		panic(err)
	}
	writeJSON("artifacts/divrem-air.json", slice)
	writeJSON("artifacts/boundaries.json", boundaries)
	counts := []map[string]any{}
	columns, staticCells := 0, 0
	for _, m := range slice.Modules {
		n := 0
		for _, c := range slice.Constraints {
			if c.Owner == m.ID {
				n++
			}
		}
		columns += len(m.Columns)
		staticCells += len(m.Content) * len(m.Columns)
		counts = append(counts, map[string]any{"id": m.ID, "name": m.Name, "columns": len(m.Columns),
			"constraints": n, "static_rows": len(m.Content)})
	}
	interfaces := []airdata.Constraint{}
	for _, c := range artifact.Constraints {
		if c.Kind != "lookup" {
			continue
		}
		for _, v := range c.Targets {
			m, ok := artifact.Module(v.Module)
			if !ok {
				panic("invalid module")
			}
			for _, root := range roots {
				if m.Name == root {
					interfaces = append(interfaces, c)
					break
				}
			}
		}
	}
	writeJSON("artifacts/helper-interfaces.json", interfaces)
	mutationPlan := []map[string]any{}
	for _, c := range slice.Constraints {
		mutationPlan = append(mutationPlan, map[string]any{"constraint_id": c.ID, "owner": c.Owner,
			"kind": c.Kind, "action": "delete", "classification": "unresolved: component theorem not built"})
	}
	writeJSON("artifacts/mutation-plan.json", mutationPlan)
	selectedSet := map[uint]bool{}
	naive := map[uint]bool{}
	for _, id := range selected {
		selectedSet[id], naive[id] = true, true
	}
	dynamicBoundaries := 0
	for _, c := range boundaries {
		for _, id := range c.Contexts() {
			m, _ := artifact.Module(id)
			if selectedSet[id] && !m.Static {
				dynamicBoundaries++
				break
			}
		}
	}
	for changed := true; changed; {
		changed = false
		for _, c := range artifact.Constraints {
			contexts := c.Contexts()
			touches := false
			for _, id := range contexts {
				touches = touches || naive[id]
			}
			if !touches {
				continue
			}
			for _, id := range contexts {
				if !naive[id] {
					naive[id], changed = true, true
				}
			}
		}
	}
	writeJSON("artifacts/closure-report.json", map[string]any{
		"roots": roots, "selected_ids": selected, "modules": counts,
		"selected_constraints": len(slice.Constraints), "selected_columns": columns,
		"static_cells": staticCells, "incoming_boundary_constraints": len(boundaries),
		"dynamic_incoming_constraints":        dynamicBoundaries,
		"other_users_of_static_tables":        len(boundaries) - dynamicBoundaries,
		"undirected_module_incidence_closure": len(naive),
		"full_modules":                        len(artifact.Modules), "full_constraints": len(artifact.Constraints),
		"structural_validation_errors": validationErrors,
		"component_claim":              "not proved", "production_claim": "not proved",
	})
	fmt.Printf("modules=%d constraints=%d validation_errors=%d elapsed=%s output=%s\n", len(modules), len(s.Constraints().Collect()), len(validationErrors), time.Since(started), *out)
	fmt.Printf("slice_modules=%d slice_constraints=%d columns=%d static_cells=%d boundaries=%d\n",
		len(slice.Modules), len(slice.Constraints), columns, staticCells, len(boundaries))
}

func writeJSON(path string, value any) {
	data, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		panic(err)
	}
	if err := os.WriteFile(path, append(data, '\n'), 0o644); err != nil {
		panic(err)
	}
}
