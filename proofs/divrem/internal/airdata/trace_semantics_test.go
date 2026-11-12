package airdata

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"math/rand/v2"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"testing"

	"github.com/LFDT-Lineth/lineth-monorepo/arithmetization/gopkg/embedded"
	"github.com/LFDT-Lineth/zkc/pkg/ir/air"
	"github.com/LFDT-Lineth/zkc/pkg/schema"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/checker"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/lookup"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/vanishing"
	"github.com/LFDT-Lineth/zkc/pkg/trace"
	"github.com/LFDT-Lineth/zkc/pkg/util"
	"github.com/LFDT-Lineth/zkc/pkg/util/collection/array"
	"github.com/LFDT-Lineth/zkc/pkg/util/collection/iter"
	"github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear"
)

type traceModule struct {
	ID   uint       `json:"id"`
	Rows [][]uint64 `json:"rows"`
}

type traceCase struct {
	Name             string        `json:"name"`
	Modules          []traceModule `json:"modules"`
	StaticTables     []traceModule `json:"static_tables,omitempty"`
	ExpectedAccepted *bool         `json:"expected_accepted,omitempty"`
}

type traceVerdict struct {
	Name     string `json:"name"`
	Accepted bool   `json:"accepted"`
	Verdicts []bool `json:"verdicts"`
}

// Constraint filtering preserves the pinned upstream evaluator and module IDs.
// Synthetic range-table cases override static contents on isolated table copies.
type traceSliceSchema struct {
	schema.Schema[koalabear.Element]
	selected []schema.Constraint[koalabear.Element]
}

func (s traceSliceSchema) Constraints() iter.Iterator[schema.Constraint[koalabear.Element]] {
	return iter.NewArrayIterator(s.selected)
}

func TestTraceSemanticsAgainstZkC(t *testing.T) {
	exe := os.Getenv("DIVREM_SEMANTICS_EXE")
	if exe == "" {
		t.Skip("run by LinuxBuild.py after building trace_semantics")
	}
	exe, err := filepath.Abs(exe)
	if err != nil {
		t.Fatal(err)
	}
	base, err := filepath.Abs("../../artifacts")
	if err != nil {
		t.Fatal(err)
	}
	write := func(name string, value any) string {
		t.Helper()
		data, err := json.Marshal(value)
		if err != nil {
			t.Fatal(err)
		}
		path := filepath.Join(base, name)
		if err := os.WriteFile(path, append(data, '\n'), 0644); err != nil {
			t.Fatal(err)
		}
		return path
	}
	run := func(args ...string) {
		t.Helper()
		if output, err := exec.Command(exe, args...).CombinedOutput(); err != nil {
			t.Fatalf("Lean trace checker: %v\n%s", err, output)
		} else {
			t.Log(string(output))
		}
	}
	rng := rand.New(rand.NewPCG(7, 19))
	edges := []uint64{0, 1, 2, 3, 65535, 65536, 1 << 31, 1<<32 - 1,
		1 << 32, 1<<63 - 1, 1 << 63, 1<<63 + 1, ^uint64(0) - 1, ^uint64(0)}
	pairs := [][2]uint64{}
	for _, a := range edges {
		for _, b := range edges {
			pairs = append(pairs, [2]uint64{a, b})
		}
	}
	for len(pairs) < 256 {
		pairs = append(pairs, [2]uint64{rng.Uint64(), rng.Uint64()})
	}
	input := write("trace-pairs.json", map[string]any{"pairs": pairs})
	witnessPath := filepath.Join(base, "trace-witnesses.json")
	run("--witnesses", input, witnessPath)
	var corpus struct {
		Cases []traceCase `json:"cases"`
	}
	data, err := os.ReadFile(witnessPath)
	if err != nil {
		t.Fatal(err)
	}
	if err := json.Unmarshal(data, &corpus); err != nil || len(corpus.Cases) != len(pairs) {
		t.Fatalf("witness corpus: %v", err)
	}
	bin, err := embedded.CompiledBinaryFile()
	if err != nil {
		t.Fatal(err)
	}
	upstream := bin.AirConstraints()
	artifact, err := Export(upstream)
	if err != nil {
		t.Fatal(err)
	}
	slice, _, _, err := artifact.Slice([]string{"divMod_64_uu", "divMod_64_ss", "divMod_32_uu", "divMod_32_ss"})
	if err != nil || len(slice.Constraints) != 548 {
		t.Fatalf("slice: %v", err)
	}
	selected := []schema.Constraint[koalabear.Element]{}
	all := upstream.Constraints().Collect()
	for _, c := range slice.Constraints {
		// Upstream reuses lookup handles for separate calls to one helper.
		// Give shallow copies unique diagnostic labels. Expressions, domains,
		// selectors and port arrays remain the exact upstream objects.
		handle := fmt.Sprintf("trace-id-%d", c.ID)
		switch original := all[c.ID].(type) {
		case *vanishing.Constraint[koalabear.Element, air.LogicalTerm[koalabear.Element]]:
			copy := *original
			copy.Handle = handle
			selected = append(selected, &copy)
		case *lookup.Constraint[koalabear.Element]:
			copy := *original
			copy.Handle = handle
			selected = append(selected, &copy)
		default:
			t.Fatalf("unsupported differential constraint %T", original)
		}
	}
	sc := traceSliceSchema{upstream, selected}
	clone := func(c traceCase) traceCase {
		out := traceCase{Name: c.Name}
		for _, m := range c.Modules {
			rows := make([][]uint64, len(m.Rows))
			for i := range rows {
				rows[i] = slices.Clone(m.Rows[i])
			}
			out.Modules = append(out.Modules, traceModule{m.ID, rows})
		}
		return out
	}
	honest := len(corpus.Cases)
	columns := map[uint]map[int]bool{}
	for i := range honest {
		for j := range 9 {
			c := clone(corpus.Cases[i])
			c.Name = fmt.Sprintf("cell-mutation-%d-%d", i, j)
			m := &c.Modules[(i+j)%len(c.Modules)]
			row := (i + j) % len(m.Rows)
			col := (i*9 + j) % len(m.Rows[row])
			if columns[m.ID] == nil {
				columns[m.ID] = map[int]bool{}
			}
			columns[m.ID][col] = true
			m.Rows[row][col] = (m.Rows[row][col] + 1) % Modulus
			corpus.Cases = append(corpus.Cases, c)
		}
	}
	for i := range 768 {
		c := clone(corpus.Cases[i%honest])
		c.Name = fmt.Sprintf("random-%d", i)
		for mi := range c.Modules {
			m := &c.Modules[mi]
			width := len(m.Rows[0])
			m.Rows = make([][]uint64, 1+rng.IntN(3))
			for row := range m.Rows {
				m.Rows[row] = make([]uint64, width)
				for col := range m.Rows[row] {
					m.Rows[row][col] = rng.Uint64N(Modulus)
				}
			}
		}
		corpus.Cases = append(corpus.Cases, c)
	}
	// Noncanonical limbs and non-Boolean gates are canonical field values.
	for _, mutation := range []struct {
		col   int
		value uint64
	}{{0, 65536}, {43, 0}, {43, 2}, {8, 65536}, {12, Modulus - 1}} {
		c := clone(corpus.Cases[0])
		c.Name = fmt.Sprintf("targeted-62-%d-%d", mutation.col, mutation.value)
		for _, m := range c.Modules {
			if m.ID == 62 {
				m.Rows[0][mutation.col] = mutation.value
			}
		}
		corpus.Cases = append(corpus.Cases, c)
	}
	tableCase := func(name string, tables []traceModule, expected bool, wrongRemainder bool) {
		c := clone(corpus.Cases[0]) // 0 / 0, with both signed helpers active.
		c.Name, c.StaticTables, c.ExpectedAccepted = name, tables, &expected
		if wrongRemainder {
			for _, m := range c.Modules {
				if m.ID == 62 {
					m.Rows[0][15] = 1
				}
			}
		}
		corpus.Cases = append(corpus.Cases, c)
	}
	wide, ok := slice.Module(98)
	if !ok {
		t.Fatal("16-bit range table missing")
	}
	duplicate := append(slices.Clone(wide.Content), []uint64{0})
	without := func(value uint64) [][]uint64 {
		rows := [][]uint64{}
		for _, row := range wide.Content {
			if row[0] != value {
				rows = append(rows, row)
			}
		}
		return rows
	}
	allDuplicated := []traceModule{}
	for _, m := range slice.Modules {
		if m.Static {
			allDuplicated = append(allDuplicated, traceModule{m.ID, append(slices.Clone(m.Content), m.Content...)})
		}
	}
	tableCase("table-duplicate-zero", []traceModule{{98, duplicate}}, true, false)
	tableCase("table-duplicate-all", allDuplicated, true, false)
	tableCase("table-missing-unused", []traceModule{{98, without(12345)}}, true, false)
	tableCase("table-missing-required", []traceModule{{98, without(0)}}, false, false)
	tableCase("table-empty", []traceModule{{98, [][]uint64{}}}, false, false)
	tableCase("table-duplicate-and-missing", []traceModule{{98, append(without(0), []uint64{65535})}}, false, false)
	tableCase("table-duplicate-wrong-remainder", []traceModule{{98, duplicate}}, false, true)
	tableCase("table-missing-unused-wrong-remainder", []traceModule{{98, without(12345)}}, false, true)
	corpusPath := write("trace-corpus.json", corpus)
	resultPath := filepath.Join(base, "trace-lean-results.json")
	run(filepath.Join(base, "air.wire"), corpusPath, resultPath)
	data, err = os.ReadFile(resultPath)
	if err != nil {
		t.Fatal(err)
	}
	var lean struct {
		Results []traceVerdict `json:"results"`
	}
	if err := json.Unmarshal(data, &lean); err != nil || len(lean.Results) != len(corpus.Cases) {
		t.Fatalf("Lean verdict corpus: %v", err)
	}
	accepted, rejected := 0, 0
	tableResults := []map[string]any{}
	coverage := make([][2]int, len(slice.Constraints))
	for ci, c := range corpus.Cases {
		modules := make([]trace.Module[koalabear.Element], upstream.Width())
		for mid, m := range upstream.Modules().Collect() {
			rows := [][]uint64{}
			for _, data := range c.Modules {
				if data.ID == uint(mid) {
					rows = data.Rows
				}
			}
			cols := []array.Array[koalabear.Element]{}
			descriptors := []trace.ColumnDescriptor{}
			for col, reg := range m.Registers() {
				values := make([]koalabear.Element, len(rows))
				for row := range rows {
					values[row] = koalabear.New(uint32(rows[row][col]))
				}
				cols = append(cols, array.NewStaticArray(31, values...))
				descriptors = append(descriptors, trace.NewColumnDescriptor(reg.Name(), util.None[uint]()))
			}
			modules[mid] = trace.NewModule(trace.NewModuleDescriptor(m.Name(), descriptors), cols...)
		}
		shard := trace.NewShard(modules)
		caseSchema := sc
		if len(c.StaticTables) != 0 {
			// ZkC reads static lookup contents from the schema, not the trace.
			copies := slices.Clone(upstream.RawModules())
			for _, table := range c.StaticTables {
				m, ok := slice.Module(table.ID)
				if !ok || !m.Static || len(m.Columns) != 1 || m.Columns[0].Bits == nil {
					t.Fatalf("invalid range-table override %d", table.ID)
				}
				contents := make([][]koalabear.Element, len(table.Rows))
				for i, row := range table.Rows {
					if len(row) != 1 || row[0] >= 1<<*m.Columns[0].Bits {
						t.Fatalf("override %d is not range-safe", table.ID)
					}
					contents[i] = []koalabear.Element{koalabear.New(uint32(row[0]))}
				}
				copy := *copies[table.ID]
				copy.SetStaticContents(contents)
				copies[table.ID] = &copy
			}
			caseSchema = traceSliceSchema{schema.NewUniformSchema[koalabear.Element](copies), selected}
		}
		failures, errors := checker.New[koalabear.Element](caseSchema).WithParallelism(false).CheckStrict(trace.Trace[koalabear.Element]{shard})
		if len(errors) != 0 {
			t.Fatalf("upstream checker errors in %s: %v", c.Name, errors)
		}
		failed := map[string]bool{}
		for _, f := range failures {
			failed[f.Handle()] = true
		}
		verdicts := make([]bool, len(slice.Constraints))
		for i, c := range slice.Constraints {
			handle := fmt.Sprintf("trace-id-%d", c.ID)
			if c.Kind == "vanishing" {
				handle = constraint.DetermineHandle(handle, c.Owner, shard)
			}
			verdicts[i] = !failed[handle]
			bucket := 0
			if verdicts[i] {
				bucket = 1
			}
			coverage[i][bucket]++
		}
		verdict := lean.Results[ci]
		if verdict.Name != c.Name || verdict.Accepted != (len(failures) == 0) || !slices.Equal(verdict.Verdicts, verdicts) {
			messages := []string{}
			for _, f := range failures {
				messages = append(messages, f.Message())
			}
			path := write("trace-disagreement.json", map[string]any{"case": c, "lean": verdict, "upstream": verdicts, "failures": messages})
			t.Fatalf("evaluator disagreement in %s; saved %s", c.Name, path)
		}
		if len(failures) == 0 {
			accepted++
		} else {
			rejected++
		}
		if ci < honest && len(failures) != 0 {
			t.Fatalf("honest witness %s rejected: %v", c.Name, failures)
		}
		if c.ExpectedAccepted != nil {
			if verdict.Accepted != *c.ExpectedAccepted {
				t.Fatalf("%s: expected acceptance %v, got %v", c.Name, *c.ExpectedAccepted, verdict.Accepted)
			}
			tableResults = append(tableResults, map[string]any{"name": c.Name, "accepted": verdict.Accepted,
				"expected_accepted": *c.ExpectedAccepted, "overridden_tables": len(c.StaticTables)})
		}
		if (ci+1)%256 == 0 {
			t.Logf("compared %d/%d traces", ci+1, len(corpus.Cases))
		}
	}
	wire, err := os.ReadFile(filepath.Join(base, "air.wire"))
	if err != nil {
		t.Fatal(err)
	}
	digest := sha256.Sum256(wire)
	write("trace-semantics-summary.json", map[string]any{
		"status": "passed", "traces": len(corpus.Cases), "honest": honest,
		"cell_mutations": honest * 9, "random": 768, "targeted": 5,
		"range_safe_table_variants": tableResults,
		"accepted":                  accepted, "rejected": rejected, "disagreements": 0,
		"seed": []uint64{7, 19}, "constraints": len(slice.Constraints),
		"constraint_verdicts": len(corpus.Cases) * len(slice.Constraints),
		"constraint_ids": func() []uint {
			out := []uint{}
			for _, c := range slice.Constraints {
				out = append(out, c.ID)
			}
			return out
		}(),
		"constraint_coverage_reject_accept": coverage, "mutated_columns": columns,
		"wire_sha256": hex.EncodeToString(digest[:]),
		"scope":       "differential evidence for the selected unsharded slice with canonical and synthetic range-safe tables; isolated schema copies override static contents, captured AIR unchanged; not evaluator equivalence or backend verification",
	})
	t.Logf("%d traces: %d accepted, %d rejected; %d per-constraint verdicts agree", len(corpus.Cases), accepted, rejected, len(corpus.Cases)*len(slice.Constraints))
}
