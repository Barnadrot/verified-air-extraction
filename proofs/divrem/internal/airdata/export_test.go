package airdata

import (
	"encoding/json"
	"math/rand/v2"
	"os"
	"testing"

	"github.com/LFDT-Lineth/lineth-monorepo/arithmetization/gopkg/embedded"
	"github.com/LFDT-Lineth/zkc/pkg/ir/air"
	"github.com/LFDT-Lineth/zkc/pkg/trace"
	"github.com/LFDT-Lineth/zkc/pkg/util"
	"github.com/LFDT-Lineth/zkc/pkg/util/collection/array"
	"github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear"
)

// The explicit capture parameter is the same Go type as the upstream AIR schema.
var _ func(air.Schema[koalabear.Element]) (Artifact, error) = Export

func TestExportedExpressionsAgainstZkC(t *testing.T) {
	bin, err := embedded.CompiledBinaryFile()
	if err != nil {
		t.Fatal(err)
	}
	schema := bin.AirConstraints()
	artifact, err := Export(schema)
	if err != nil {
		t.Fatal(err)
	}
	slice, _, ids, err := artifact.Slice([]string{"divMod_64_uu", "divMod_64_ss", "divMod_32_uu", "divMod_32_ss"})
	if err != nil {
		t.Fatal(err)
	}
	selected := map[uint]bool{}
	for _, id := range ids {
		selected[id] = true
	}
	_ = slice
	vectors := ExpressionVectors{Format: "divrem-expression-vectors-v1", Cases: []ExpressionVector{}}
	wireVectors := []struct {
		Expr  Term   `json:"expr"`
		Bytes []uint `json:"bytes"`
	}{}
	extraShiftCases := 0
	rng := rand.New(rand.NewPCG(7, 19))
	checked := 0
	for mid, m := range schema.Modules().Collect() {
		rows := make([][]uint64, 4)
		for row := range rows {
			rows[row] = make([]uint64, len(m.Registers()))
		}
		columns := []array.Array[koalabear.Element]{}
		descriptors := []trace.ColumnDescriptor{}
		for col, r := range m.Registers() {
			values := make([]koalabear.Element, len(rows))
			for row := range rows {
				v := rng.Uint64N(Modulus)
				if row == 0 {
					v = 0
				}
				if row == 1 {
					v = Modulus - 1
				}
				rows[row][col] = v
				values[row] = koalabear.New(uint32(v))
			}
			columns = append(columns, array.NewStaticArray(31, values...))
			descriptors = append(descriptors, trace.NewColumnDescriptor(r.Name(), util.None[uint]()))
		}
		tr := trace.NewModule(trace.NewModuleDescriptor(m.Name(), descriptors), columns...)
		for _, raw := range m.Constraints().Collect() {
			c, ok := raw.(*air.VanishingConstraint[koalabear.Element])
			if !ok {
				continue
			}
			exported, err := ExportTerm(c.Constraint.Term)
			if err != nil {
				t.Fatal(err)
			}
			encoded, err := json.Marshal(exported)
			if err != nil {
				t.Fatal(err)
			}
			var decoded Term
			if err := json.Unmarshal(encoded, &decoded); err != nil {
				t.Fatal(err)
			}
			vector := ExpressionVector{Expr: decoded, Rows: rows, Expected: []Evaluation{}}
			for row := -1; row <= len(rows); row++ {
				want, err := c.Constraint.Term.EvalAt(uint(row), tr, m)
				if err != nil {
					t.Fatal(err)
				}
				got, err := decoded.Eval(rows, row)
				if err != nil {
					t.Fatal(err)
				}
				if got != want.Uint64() {
					t.Fatalf("%s:%s row %d: got %d want %d", m.Name(), c.Name(), row, got, want.Uint64())
				}
				checked++
				vector.Expected = append(vector.Expected, Evaluation{Row: row, Value: want.Uint64()})
			}
			included := selected[uint(mid)]
			if included {
				vectors.Cases = append(vectors.Cases, vector)
			} else if decoded.HasShift() && extraShiftCases < 16 {
				vectors.Cases = append(vectors.Cases, vector)
				extraShiftCases++
				included = true
			}
			if included {
				wire, err := EncodeTermWire(decoded)
				if err != nil {
					t.Fatal(err)
				}
				bytes := make([]uint, len(wire))
				for i, b := range wire {
					bytes[i] = uint(b)
				}
				wireVectors = append(wireVectors, struct {
					Expr  Term   `json:"expr"`
					Bytes []uint `json:"bytes"`
				}{decoded, bytes})
			}
		}
	}
	t.Logf("compared %d expression evaluations after JSON serialization", checked)
	encoded, err := json.Marshal(vectors)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll("../../artifacts", 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile("../../artifacts/expression-vectors.json", encoded, 0o644); err != nil {
		t.Fatal(err)
	}
	t.Logf("wrote %d expression vectors for Lean, including %d shifted expressions outside the slice", len(vectors.Cases), extraShiftCases)
	if len(wireVectors) != len(vectors.Cases) {
		t.Fatal("wire vector set differs")
	}
	wireJSON, err := json.Marshal(wireVectors)
	if err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile("../../artifacts/term-wire-vectors.json", wireJSON, 0o644); err != nil {
		t.Fatal(err)
	}
}

func TestStaticDependencyDoesNotImportOtherUsers(t *testing.T) {
	bits := uint(16)
	col := Column{ID: 0, Bits: &bits}
	a := Artifact{Format: "divrem-air-v1", Field: "KOALABEAR_16", Modulus: Modulus,
		Modules: []Module{{ID: 0, Name: "root", Columns: []Column{col}},
			{ID: 1, Name: "table", Static: true, Columns: []Column{col}, Content: [][]uint64{{0}}},
			{ID: 2, Name: "other", Columns: []Column{col}}},
		Constraints: []Constraint{
			{ID: 0, Owner: 0, Kind: "lookup", Sources: []Vector{{Module: 0, Columns: []uint{0}}}, Targets: []Vector{{Module: 1, Columns: []uint{0}}}},
			{ID: 1, Owner: 2, Kind: "lookup", Sources: []Vector{{Module: 2, Columns: []uint{0}}}, Targets: []Vector{{Module: 1, Columns: []uint{0}}}},
		}}
	slice, boundaries, _, err := a.Slice([]string{"root"})
	if err != nil {
		t.Fatal(err)
	}
	if len(slice.Modules) != 2 || len(slice.Constraints) != 1 || len(boundaries) != 1 || boundaries[0].ID != 1 {
		t.Fatal("shared table imported an unrelated caller or hid its boundary")
	}
	a.Constraints[0].Targets[0].Columns[0] = 99
	if a.Validate() == nil {
		t.Fatal("invalid reference accepted")
	}
	a.Constraints[0].Kind = "unknown"
	if a.Validate() == nil {
		t.Fatal("unknown constraint accepted")
	}
}
