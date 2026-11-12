package airdata

import (
	"github.com/LFDT-Lineth/zkc/pkg/ir/air"
	"github.com/LFDT-Lineth/zkc/pkg/ir/term"
	"github.com/LFDT-Lineth/zkc/pkg/schema"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/bus"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/lookup"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/ranged"
	"github.com/LFDT-Lineth/zkc/pkg/schema/constraint/vanishing"
	"github.com/LFDT-Lineth/zkc/pkg/schema/register"
	"github.com/LFDT-Lineth/zkc/pkg/util"
	"github.com/LFDT-Lineth/zkc/pkg/util/field/koalabear"
)

func uintRef(r register.Id) *uint { v := r.Unwrap(); return &v }

func lookupVector(v lookup.Vector) Vector {
	out := Vector{Module: v.Module, Columns: exportColumnIDs(v.Registers)}
	if v.Selector.HasValue() {
		out.Selector = uintRef(v.Selector.Unwrap())
	}
	return out
}

func busVector(v bus.Port) Vector {
	return Vector{Module: v.Module, Selector: uintRef(v.Selector), Columns: exportColumnIDs(v.Registers)}
}

func exportColumnIDs(registers []register.Id) []uint {
	out := []uint{}
	for _, r := range registers {
		out = append(out, r.Unwrap())
	}
	return out
}

func ExportTerm(t air.Term[koalabear.Element]) (Term, error) {
	out := Term{Args: []Term{}}
	var args []air.Term[koalabear.Element]
	switch t := t.(type) {
	case *term.Constant[koalabear.Element, air.Term[koalabear.Element]]:
		out.Kind, out.Value = "constant", t.Value.Uint64()
	case *term.RegisterAccess[koalabear.Element, air.Term[koalabear.Element]]:
		out.Kind, out.Column, out.Shift = "column", t.Register().Unwrap(), t.RelativeShift()
	case *term.Add[koalabear.Element, air.Term[koalabear.Element]]:
		out.Kind, args = "add", t.Args
	case *term.Sub[koalabear.Element, air.Term[koalabear.Element]]:
		out.Kind, args = "sub", t.Args
	case *term.Mul[koalabear.Element, air.Term[koalabear.Element]]:
		out.Kind, args = "mul", t.Args
	default:
		return out, captureError("unsupported AIR term")
	}
	for _, arg := range args {
		v, err := ExportTerm(arg)
		if err != nil {
			return out, err
		}
		out.Args = append(out.Args, v)
	}
	return out, nil
}

// Spell out air.Schema's alias so the source translator sees the concrete data type.
func Export(s schema.UniformSchema[koalabear.Element, *schema.Table[koalabear.Element, schema.Constraint[koalabear.Element]]]) (Artifact, error) {
	out := Artifact{Format: "divrem-air-v1", Field: "KOALABEAR_16", Modulus: Modulus,
		Modules: exportModules(s.RawModules())}
	var err error
	out.Constraints, err = exportAllConstraints(s.RawModules())
	return out, err
}

func exportModules(modules []*schema.Table[koalabear.Element, schema.Constraint[koalabear.Element]]) []Module {
	out := []Module{}
	for mid, m := range modules {
		out = append(out, exportModule(uint(mid), m))
	}
	return out
}

func exportModuleConstraints(mid, first uint, constraints []schema.Constraint[koalabear.Element]) ([]Constraint, error) {
	out := []Constraint{}
	for index, source := range constraints {
		c, err := exportConstraint(mid, first+uint(index), source)
		if err != nil {
			return nil, err
		}
		out = append(out, c)
	}
	return out, nil
}

func exportAllConstraints(modules []*schema.Table[koalabear.Element, schema.Constraint[koalabear.Element]]) ([]Constraint, error) {
	out := []Constraint{}
	for mid, m := range modules {
		constraints, err := exportModuleConstraints(uint(mid), uint(len(out)), m.RawConstraints())
		if err != nil {
			return nil, err
		}
		out = append(out, constraints...)
	}
	return out, nil
}

func exportColumn(id uint, r register.Register) Column {
	col := Column{ID: id, Name: r.Name(), Input: r.IsInput(), Output: r.IsOutput(), Native: r.IsNative()}
	if !r.IsNative() {
		width := r.Width()
		col.Bits = &width
	}
	return col
}

func exportStaticRow(row []koalabear.Element) []uint64 {
	values := []uint64{}
	for _, value := range row {
		values = append(values, value.Uint64())
	}
	return values
}

func exportModule(mid uint, m *schema.Table[koalabear.Element, schema.Constraint[koalabear.Element]]) Module {
	mod := Module{ID: mid, Name: m.Name(), Static: m.IsStatic(), Native: m.IsNative(),
		Columns: []Column{}, Content: [][]uint64{}}
	mod.Columns = exportColumns(m.Registers())
	if m.IsStatic() {
		mod.Content = exportStaticRows(m.StaticContents())
	}
	return mod
}

func exportColumns(registers []register.Register) []Column {
	columns := []Column{}
	for rid, r := range registers {
		columns = append(columns, exportColumn(uint(rid), r))
	}
	return columns
}

func exportStaticRows(rows [][]koalabear.Element) [][]uint64 {
	values := [][]uint64{}
	for _, row := range rows {
		values = append(values, exportStaticRow(row))
	}
	return values
}

func exportConstraint(mid, id uint, cs schema.Constraint[koalabear.Element]) (Constraint, error) {
	c := Constraint{ID: id, Owner: mid, Sources: []Vector{}, Targets: []Vector{}}
	switch cs := cs.(type) {
	case *vanishing.Constraint[koalabear.Element, air.LogicalTerm[koalabear.Element]]:
		c.Name = cs.Name()
		if cs.Context != mid {
			return c, captureError("vanishing owner mismatch")
		}
		c.Kind = "vanishing"
		c.Domain = exportDomain(cs.Domain)
		expr, err := ExportTerm(cs.Constraint.Term)
		if err != nil {
			return c, err
		}
		c.Expr = &expr
	case *ranged.Constraint[koalabear.Element]:
		c.Name = cs.Name()
		if cs.Context != mid {
			return c, captureError("range owner mismatch")
		}
		c.Kind, c.Column, c.Bits = "range", cs.Source.Unwrap(), cs.Bitwidth
	case *lookup.Constraint[koalabear.Element]:
		c.Name = cs.Name()
		c.Kind = "lookup"
		c.Sources = exportLookupVectors(cs.Sources)
		c.Targets = exportLookupVectors(cs.Targets)
	case *bus.Constraint[koalabear.Element]:
		c.Name = cs.Name()
		c.Kind = "bus"
		c.Sources = exportBusPorts(cs.Sends)
		c.Targets = exportBusPorts(cs.Receives)
	default:
		return c, captureError("unsupported AIR constraint")
	}
	return c, nil
}

func exportDomain(domain util.Option[int]) *int {
	if !domain.HasValue() {
		return nil
	}
	value := domain.Unwrap()
	return &value
}

func exportLookupVectors(vectors []lookup.Vector) []Vector {
	out := []Vector{}
	for _, v := range vectors {
		out = append(out, lookupVector(v))
	}
	return out
}

func exportBusPorts(ports []bus.Port) []Vector {
	out := []Vector{}
	for _, v := range ports {
		out = append(out, busVector(v))
	}
	return out
}
