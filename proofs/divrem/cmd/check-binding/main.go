package main

import (
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"

	"divremfv/internal/airdata"
)

// This exercises the compiled binding adapter. It is not a kernel proof of IO.
func main() {
	root := "artifacts/binding-tests"
	check(os.MkdirAll(root, 0o755))
	fullData := read("artifacts/air.json")
	sliceData := read("artifacts/divrem-air.json")
	interfaceData := read("artifacts/helper-interfaces.json")
	tests := []struct {
		name   string
		accept bool
		change func(*airdata.Artifact, *airdata.Artifact, *[]airdata.Constraint)
	}{
		{"unchanged", true, func(*airdata.Artifact, *airdata.Artifact, *[]airdata.Constraint) {}},
		{"column-name-update", true, func(f, s *airdata.Artifact, _ *[]airdata.Constraint) {
			for i := range s.Modules {
				if s.Modules[i].ID == 62 {
					s.Modules[i].Columns[0].Name = "renamed_input_high_limb"
					f.Modules[62].Columns[0].Name = "renamed_input_high_limb"
				}
			}
		}},
		{"wrong-polynomial", false, func(f, s *airdata.Artifact, _ *[]airdata.Constraint) {
			for i := range s.Constraints {
				if s.Constraints[i].Owner == 62 && s.Constraints[i].Kind == "vanishing" {
					s.Constraints[i].Expr = &airdata.Term{Kind: "constant", Value: 0, Args: []airdata.Term{}}
					f.Constraints[s.Constraints[i].ID] = s.Constraints[i]
					return
				}
			}
			panic("signed constraint absent")
		}},
		{"missing-constraint", false, func(_ *airdata.Artifact, s *airdata.Artifact, _ *[]airdata.Constraint) {
			s.Constraints = s.Constraints[1:]
		}},
		{"wrong-static-table", false, func(f, s *airdata.Artifact, _ *[]airdata.Constraint) {
			for i := range s.Modules {
				if s.Modules[i].Static {
					s.Modules[i].Content[0][0] = 1
					f.Modules[s.Modules[i].ID].Content[0][0] = 1
					return
				}
			}
		}},
		{"wrong-call-selector", false, func(f, _ *airdata.Artifact, calls *[]airdata.Constraint) {
			zero := uint(0)
			(*calls)[0].Targets[0].Selector = &zero
			f.Constraints[(*calls)[0].ID] = (*calls)[0]
		}},
		{"swapped-output-columns", false, func(f, _ *airdata.Artifact, calls *[]airdata.Constraint) {
			cols := (*calls)[0].Targets[0].Columns
			cols[8], cols[9] = cols[9], cols[8]
			f.Constraints[(*calls)[0].ID] = (*calls)[0]
		}},
		{"unsupported-term", false, func(_ *airdata.Artifact, s *airdata.Artifact, _ *[]airdata.Constraint) {
			s.Constraints[0].Expr.Kind = "unsupported"
		}},
	}
	results := []map[string]any{}
	for _, test := range tests {
		var full, slice airdata.Artifact
		var calls []airdata.Constraint
		check(json.Unmarshal(fullData, &full))
		check(json.Unmarshal(sliceData, &slice))
		check(json.Unmarshal(interfaceData, &calls))
		test.change(&full, &slice, &calls)
		// Semantic negative cases must remain structurally valid.
		if test.name != "unsupported-term" {
			check(full.Validate())
			check(slice.Validate())
		}
		fullPath, slicePath, callsPath := filepath.Join(root, "full.json"), filepath.Join(root, "slice.json"), filepath.Join(root, "calls.json")
		write(fullPath, full)
		write(slicePath, slice)
		write(callsPath, calls)
		binder := filepath.Join(".lake", "build", "bin", "air_bind")
		if runtime.GOOS == "windows" {
			binder += ".exe"
		}
		command := exec.Command(binder, fullPath, slicePath, callsPath)
		output, err := command.CombinedOutput()
		accepted := err == nil
		if !accepted {
			if status, ok := err.(*exec.ExitError); !ok || status.ExitCode() != 1 {
				panic(fmt.Sprintf("binding process failed: %v %s", err, output))
			}
		}
		if accepted != test.accept {
			panic(fmt.Sprintf("unexpected result for %s: %s", test.name, output))
		}
		results = append(results, map[string]any{"case": test.name, "accepted": accepted, "message": string(output)})
		fmt.Printf("binding %s: accepted=%v\n", test.name, accepted)
	}
	write("artifacts/binding-tests.json", results)
}

func read(path string) []byte { data, err := os.ReadFile(path); check(err); return data }
func write(path string, value any) {
	data, err := json.MarshalIndent(value, "", "  ")
	check(err)
	check(os.WriteFile(path, append(data, '\n'), 0o644))
}
func check(err error) {
	if err != nil {
		panic(err)
	}
}
