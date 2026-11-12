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

// Executable adversarial evidence for the binary path, separate from its proofs.
func main() {
	baseline, err := os.ReadFile("artifacts/air.json")
	check(err)
	reader := filepath.Join(".lake", "build", "bin", "artifact_reader")
	if runtime.GOOS == "windows" {
		reader += ".exe"
	}
	fixture := "artifacts/wire-binding-fixture.wire"
	defer os.Remove(fixture)
	tests := []struct {
		name   string
		accept bool
		change func(*airdata.Artifact)
	}{
		{"unchanged", true, func(*airdata.Artifact) {}},
		{"column-name-update", true, func(a *airdata.Artifact) { a.Modules[62].Columns[0].Name = "renamed_input_high_limb" }},
		{"changed-coefficient", false, func(a *airdata.Artifact) {
			for i := range a.Constraints {
				c := &a.Constraints[i]
				if c.Owner == 62 && c.Expr != nil && changeConstant(c.Expr) {
					return
				}
			}
			panic("signed helper constant absent")
		}},
		{"missing-constraint", false, func(a *airdata.Artifact) {
			for i, c := range a.Constraints {
				if c.Owner == 62 {
					a.Constraints = append(a.Constraints[:i], a.Constraints[i+1:]...)
					for j := range a.Constraints {
						a.Constraints[j].ID = uint(j)
					}
					return
				}
			}
			panic("signed helper constraint absent")
		}},
		{"changed-static-value", false, func(a *airdata.Artifact) { a.Modules[84].Content[0][0] = 1 }},
		{"changed-selector", false, func(a *airdata.Artifact) {
			port := incoming(a)
			value := uint(0)
			port.Selector = &value
		}},
		{"changed-column-order", false, func(a *airdata.Artifact) {
			columns := incoming(a).Columns
			columns[8], columns[9] = columns[9], columns[8]
		}},
		{"unsupported-term", false, func(a *airdata.Artifact) {
			for i := range a.Constraints {
				if a.Constraints[i].Owner == 62 && a.Constraints[i].Expr != nil {
					a.Constraints[i].Expr.Kind = "unsupported"
					return
				}
			}
			panic("signed helper expression absent")
		}},
	}
	results := []map[string]any{}
	for _, test := range tests {
		var artifact airdata.Artifact
		check(json.Unmarshal(baseline, &artifact))
		test.change(&artifact)
		bytes, encodeError := airdata.EncodeArtifactWire(artifact)
		accepted, stage, message := false, "Go writer", ""
		if encodeError != nil {
			message = encodeError.Error()
		} else {
			check(os.WriteFile(fixture, bytes, 0o644))
			output, runError := exec.Command(reader, fixture, "--wire-only").CombinedOutput()
			accepted, stage, message = runError == nil, "binary decoder and pure component check", string(output)
			if runError != nil {
				if exit, ok := runError.(*exec.ExitError); !ok || exit.ExitCode() != 1 {
					panic(fmt.Sprintf("checker did not return a controlled rejection: %v %s", runError, output))
				}
			}
		}
		if accepted != test.accept {
			panic(fmt.Sprintf("%s: expected accept=%v, got %v: %s", test.name, test.accept, accepted, message))
		}
		results = append(results, map[string]any{"case": test.name, "accepted": accepted, "stage": stage, "message": message})
	}
	encoded, err := json.MarshalIndent(results, "", "  ")
	check(err)
	check(os.WriteFile("artifacts/wire-binding-tests.json", append(encoded, '\n'), 0o644))
	fmt.Printf("Binary binding checks passed: %d cases\n", len(results))
}

func incoming(a *airdata.Artifact) *airdata.Vector {
	for i := range a.Constraints {
		for j := range a.Constraints[i].Targets {
			p := &a.Constraints[i].Targets[j]
			if p.Module == 62 && len(p.Columns) >= 10 {
				return p
			}
		}
	}
	panic("signed helper incoming port absent")
}

func changeConstant(t *airdata.Term) bool {
	if t.Kind == "constant" {
		t.Value = (t.Value + 1) % airdata.Modulus
		return true
	}
	for i := range t.Args {
		if changeConstant(&t.Args[i]) {
			return true
		}
	}
	return false
}

func check(err error) {
	if err != nil {
		panic(err)
	}
}
