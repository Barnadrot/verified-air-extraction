package airdata

import (
	"fmt"
	"slices"
	"sort"
)

const Modulus uint64 = 2130706433

type Term struct {
	Kind   string `json:"kind"`
	Value  uint64 `json:"value"`
	Column uint   `json:"column"`
	Shift  int    `json:"shift"`
	Args   []Term `json:"args"`
}

type Column struct {
	ID     uint   `json:"id"`
	Name   string `json:"name"`
	Bits   *uint  `json:"bits"`
	Input  bool   `json:"input"`
	Output bool   `json:"output"`
	Native bool   `json:"native"`
}

type Module struct {
	ID      uint       `json:"id"`
	Name    string     `json:"name"`
	Static  bool       `json:"static"`
	Native  bool       `json:"native"`
	Columns []Column   `json:"columns"`
	Content [][]uint64 `json:"content"`
}

type Vector struct {
	Module   uint   `json:"module"`
	Selector *uint  `json:"selector"`
	Columns  []uint `json:"columns"`
}

type Constraint struct {
	ID      uint     `json:"id"`
	Owner   uint     `json:"owner"`
	Name    string   `json:"name"`
	Kind    string   `json:"kind"`
	Domain  *int     `json:"domain"`
	Expr    *Term    `json:"expr"`
	Column  uint     `json:"column"`
	Bits    uint     `json:"bits"`
	Sources []Vector `json:"sources"`
	Targets []Vector `json:"targets"`
}

type Artifact struct {
	Format      string       `json:"format"`
	Field       string       `json:"field"`
	Modulus     uint64       `json:"modulus"`
	Modules     []Module     `json:"modules"`
	Constraints []Constraint `json:"constraints"`
}

func (a Artifact) Module(id uint) (Module, bool) {
	for _, m := range a.Modules {
		if m.ID == id {
			return m, true
		}
	}
	return Module{}, false
}

func (c Constraint) Contexts() []uint {
	ids := []uint{c.Owner}
	for _, v := range slices.Concat(c.Sources, c.Targets) {
		ids = append(ids, v.Module)
	}
	slices.Sort(ids)
	return slices.Compact(ids)
}

// Validate rejects unsupported syntax and malformed references. It is a data
// check, not a proof of functional correctness or exporter correspondence.
func (a Artifact) Validate() error {
	if a.Format != "divrem-air-v1" || a.Field != "KOALABEAR_16" || a.Modulus != Modulus {
		return fmt.Errorf("unsupported artifact format or field")
	}
	mods := map[uint]Module{}
	for _, m := range a.Modules {
		if _, duplicate := mods[m.ID]; duplicate {
			return fmt.Errorf("duplicate module %d", m.ID)
		}
		mods[m.ID] = m
		for i, col := range m.Columns {
			if col.ID != uint(i) || (col.Native == (col.Bits != nil)) {
				return fmt.Errorf("invalid column declaration in module %d", m.ID)
			}
		}
		for _, row := range m.Content {
			if !m.Static || len(row) != len(m.Columns) {
				return fmt.Errorf("invalid static row in module %d", m.ID)
			}
			for _, value := range row {
				if value >= Modulus {
					return fmt.Errorf("noncanonical static field value")
				}
			}
		}
	}
	checkRef := func(mid, col uint) error {
		m, ok := mods[mid]
		if !ok || col >= uint(len(m.Columns)) {
			return fmt.Errorf("invalid column reference %d:%d", mid, col)
		}
		return nil
	}
	var checkTerm func(uint, Term) error
	checkTerm = func(mid uint, t Term) error {
		switch t.Kind {
		case "constant":
			if t.Value >= Modulus || len(t.Args) != 0 {
				return fmt.Errorf("invalid constant")
			}
		case "column":
			if len(t.Args) != 0 {
				return fmt.Errorf("column has arguments")
			}
			return checkRef(mid, t.Column)
		case "add", "mul", "sub":
			if t.Kind == "sub" && len(t.Args) == 0 {
				return fmt.Errorf("empty subtraction")
			}
			for _, arg := range t.Args {
				if err := checkTerm(mid, arg); err != nil {
					return err
				}
			}
		default:
			return fmt.Errorf("unsupported term %q", t.Kind)
		}
		return nil
	}
	seen := map[uint]bool{}
	for _, c := range a.Constraints {
		if seen[c.ID] {
			return fmt.Errorf("duplicate constraint %d", c.ID)
		}
		seen[c.ID] = true
		if _, ok := mods[c.Owner]; !ok {
			return fmt.Errorf("unknown owner %d", c.Owner)
		}
		switch c.Kind {
		case "vanishing":
			if c.Expr == nil {
				return fmt.Errorf("missing expression")
			}
			if err := checkTerm(c.Owner, *c.Expr); err != nil {
				return err
			}
		case "range":
			if err := checkRef(c.Owner, c.Column); err != nil {
				return err
			}
		case "lookup", "bus":
			if len(c.Sources) == 0 || len(c.Targets) == 0 {
				return fmt.Errorf("missing lookup or bus side")
			}
			width := len(c.Sources[0].Columns)
			for _, v := range slices.Concat(c.Sources, c.Targets) {
				if len(v.Columns) != width {
					return fmt.Errorf("inconsistent vector width")
				}
				if _, ok := mods[v.Module]; !ok {
					return fmt.Errorf("unknown vector module")
				}
				if v.Selector != nil {
					if err := checkRef(v.Module, *v.Selector); err != nil {
						return err
					}
				} else if c.Kind == "bus" {
					return fmt.Errorf("bus selector absent")
				}
				for _, col := range v.Columns {
					if err := checkRef(v.Module, col); err != nil {
						return err
					}
				}
			}
		default:
			return fmt.Errorf("unsupported constraint %q", c.Kind)
		}
	}
	return nil
}

// Slice follows outgoing constraints of selected modules. Incoming references
// remain explicit boundary records; they are not claimed to be discharged.
func (a Artifact) Slice(roots []string) (Artifact, []Constraint, []uint, error) {
	selected := map[uint]bool{}
	for _, name := range roots {
		found := false
		for _, m := range a.Modules {
			if m.Name == name {
				selected[m.ID], found = true, true
			}
		}
		if !found {
			return Artifact{}, nil, nil, fmt.Errorf("root %q absent", name)
		}
	}
	for changed := true; changed; {
		changed = false
		for _, c := range a.Constraints {
			if !selected[c.Owner] {
				continue
			}
			for _, id := range c.Contexts() {
				if !selected[id] {
					selected[id], changed = true, true
				}
			}
		}
	}
	result := Artifact{Format: a.Format, Field: a.Field, Modulus: a.Modulus,
		Modules: []Module{}, Constraints: []Constraint{}}
	boundaries := []Constraint{}
	ids := []uint{}
	for _, m := range a.Modules {
		if selected[m.ID] {
			result.Modules = append(result.Modules, m)
			ids = append(ids, m.ID)
		}
	}
	for _, c := range a.Constraints {
		if selected[c.Owner] {
			result.Constraints = append(result.Constraints, c)
		} else {
			for _, id := range c.Contexts() {
				if selected[id] {
					boundaries = append(boundaries, c)
					break
				}
			}
		}
	}
	sort.Slice(ids, func(i, j int) bool { return ids[i] < ids[j] })
	return result, boundaries, ids, result.Validate()
}
