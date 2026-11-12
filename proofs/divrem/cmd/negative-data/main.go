package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"

	"divremfv/internal/airdata"
)

func main() {
	data, err := os.ReadFile("artifacts/divrem-air.json")
	if err != nil {
		panic(err)
	}
	if err := os.MkdirAll("artifacts/negative", 0o755); err != nil {
		panic(err)
	}
	cases := []struct {
		name   string
		change func(*airdata.Artifact)
	}{
		{"unknown-constraint", func(a *airdata.Artifact) { a.Constraints[0].Kind = "unsupported" }},
		{"invalid-column", func(a *airdata.Artifact) {
			a.Constraints[0].Expr = &airdata.Term{Kind: "column", Column: 999999, Args: []airdata.Term{}}
		}},
		{"noncanonical-constant", func(a *airdata.Artifact) {
			a.Constraints[0].Expr = &airdata.Term{Kind: "constant", Value: airdata.Modulus, Args: []airdata.Term{}}
		}},
		{"wrong-range-table", func(a *airdata.Artifact) {
			for i := range a.Modules {
				if a.Modules[i].Static {
					a.Modules[i].Content[0][0] = 1
					return
				}
			}
			panic("static range table absent")
		}},
	}
	for _, c := range cases {
		var a airdata.Artifact
		if err := json.Unmarshal(data, &a); err != nil {
			panic(err)
		}
		c.change(&a)
		out, err := json.Marshal(a)
		if err != nil {
			panic(err)
		}
		path := filepath.Join("artifacts/negative", c.name+".json")
		if err := os.WriteFile(path, out, 0o644); err != nil {
			panic(err)
		}
		fmt.Println(path)
	}
	vectorData, err := os.ReadFile("artifacts/expression-vectors.json")
	if err != nil {
		panic(err)
	}
	var vectors airdata.ExpressionVectors
	if err := json.Unmarshal(vectorData, &vectors); err != nil {
		panic(err)
	}
	vectors.Cases[0].Expected[0].Value = (vectors.Cases[0].Expected[0].Value + 1) % airdata.Modulus
	wrong, err := json.Marshal(vectors)
	if err != nil {
		panic(err)
	}
	if err := os.WriteFile("artifacts/negative-expression.json", wrong, 0o644); err != nil {
		panic(err)
	}
}
