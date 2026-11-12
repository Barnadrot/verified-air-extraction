package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"math/big"
	"os"
	"strings"

	"divremfv/internal/airdata"
)

func main() {
	extended := flag.Bool("extended", false, "also regenerate optional instruction and full-AIR extension data")
	flag.Parse()
	data, err := os.ReadFile("artifacts/divrem-air.json")
	check(err)
	var a airdata.Artifact
	check(json.Unmarshal(data, &a))
	check(a.Validate())
	writeArtifact(a)
	writeIntegerRows(a)
	writeUnsigned64(a)
	writeNegation(a)
	writeCalls(a)
	writeSignedCalls(a)
	writeConstruction(a)
	writeBoundsMap(a)
	writeReverseRows(a)
	writeWitnessRows(a)
	writeIncoming()
	writeNativeData(a)
	if *extended {
		writeSignExtension()
		writeInstruction()
		writeFullData(a)
	}
	fmt.Printf("Reified %d constraints as Lean data. Capture correspondence remains an explicit obligation.\n", len(a.Constraints))
}

func writeArtifact(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.RowSemantics\n\nset_option maxRecDepth 4096\nset_option maxHeartbeats 2000000\n\nnamespace DivRemFV.Generated\n\n")
	for _, c := range a.Constraints {
		fmt.Fprintf(&out, "def c%d : Constraint := %s\n", c.ID, constraint(c))
	}
	out.WriteString("\ndef constraints : List Constraint := [\n")
	for i, c := range a.Constraints {
		if i != 0 {
			out.WriteString(",\n")
		}
		fmt.Fprintf(&out, "  c%d", c.ID)
	}
	out.WriteString("\n]\n\n")
	for index, c := range a.Constraints {
		fmt.Fprintf(&out, "theorem member%d : c%d ∈ constraints := List.getElem_mem (l := constraints) (n := %d) (by decide)\n", c.ID, c.ID, index)
	}
	for _, m := range a.Modules {
		if m.Static {
			continue
		}
		fmt.Fprintf(&out, "structure Equations%d (v : Nat → K) : Prop where\n", m.ID)
		for _, c := range a.Constraints {
			if c.Owner != m.ID || c.Kind != "vanishing" {
				continue
			}
			fmt.Fprintf(&out, "  h%d : %s = 0\n", c.ID, algebra(*c.Expr))
		}
		fmt.Fprintf(&out, "\ntheorem equations%d (tables : Tables) (row : Nat)\n    (inside : row < (tables %d).size) (accepted : ConstraintsHold tables constraints) :\n    Equations%d (fun col => ((readCell tables %d col row).val : K)) := by\n  constructor\n", m.ID, m.ID, m.ID, m.ID)
		for _, c := range a.Constraints {
			if c.Owner != m.ID || c.Kind != "vanishing" {
				continue
			}
			if c.Domain != nil {
				panic("local domain in helper")
			}
			fmt.Fprintf(&out, "  · have h := accepted c%d member%d\n    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)\n    have cast := congrArg (fun n : Nat => (n : K)) value\n    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast\n", c.ID, c.ID)
		}
		fmt.Fprintf(&out, "\nstructure Bounds%d (v : Nat → Nat) : Prop where\n", m.ID)
		for _, col := range m.Columns {
			if col.Bits != nil && findRange(a, m.ID, col) != nil {
				fmt.Fprintf(&out, "  b%d : v %d < %d\n", col.ID, col.ID, uint64(1)<<*col.Bits)
			}
		}
		fmt.Fprintf(&out, "\ntheorem bounds%d (tables : Tables) (row : Nat)\n    (inside : row < (tables %d).size) (accepted : ConstraintsHold tables constraints)\n    (ranges : StaticRanges tables) :\n    Bounds%d (fun col => (readCell tables %d col row).val) := by\n  have equations := equations%d tables row inside accepted\n  constructor\n", m.ID, m.ID, m.ID, m.ID, m.ID)
		for _, col := range m.Columns {
			if col.Bits == nil {
				continue
			}
			rangeC := findRange(a, m.ID, col)
			if rangeC == nil {
				continue
			}
			if *col.Bits == 0 {
				fmt.Fprintf(&out, "  · have h : ((readCell tables %d %d row).val : K) = 0 := by simpa using equations.h%d\n    have zero := scalar_zero_of_cast_zero h\n    omega\n", m.ID, col.ID, rangeC.ID)
			} else if *col.Bits == 1 {
				fmt.Fprintf(&out, "  · exact scalar_boolean_bound (readCell tables %d %d row) (by simpa only [zero_add, one_mul] using equations.h%d)\n", m.ID, col.ID, rangeC.ID)
			} else {
				target := rangeC.Targets[0]
				fmt.Fprintf(&out, "  · exact lookup_range_bound tables %d %d %d %d row inside\n      (by simpa only [c%d] using accepted c%d member%d) (ranges %d %d (by decide))\n", m.ID, col.ID, target.Module, *col.Bits, rangeC.ID, rangeC.ID, rangeC.ID, target.Module, *col.Bits)
			}
		}
		out.WriteString("\n")
	}
	out.WriteString("end DivRemFV.Generated\n")

	writeScoped("Artifact", out.String())
}

type limits struct{ low, high *big.Int }

func number(v int64) *big.Int { return big.NewInt(v) }

func expressionLimits(t airdata.Term, columns []int64) limits {
	switch t.Kind {
	case "constant":
		value := int64(t.Value)
		if t.Value == airdata.Modulus-1 {
			value = -1
		}
		return limits{number(value), number(value)}
	case "column":
		if t.Shift != 0 {
			panic("shifted row expression")
		}
		return limits{number(0), number(columns[t.Column])}
	case "add", "sub", "mul":
		args := t.Args
		value := limits{number(0), number(0)}
		if t.Kind == "mul" {
			value = limits{number(1), number(1)}
		}
		if t.Kind == "sub" {
			value = expressionLimits(args[0], columns)
			args = args[1:]
		}
		for _, arg := range args {
			next := expressionLimits(arg, columns)
			switch t.Kind {
			case "add":
				value = limits{new(big.Int).Add(value.low, next.low), new(big.Int).Add(value.high, next.high)}
			case "sub":
				value = limits{new(big.Int).Sub(value.low, next.high), new(big.Int).Sub(value.high, next.low)}
			case "mul":
				corners := []*big.Int{new(big.Int).Mul(value.low, next.low), new(big.Int).Mul(value.low, next.high), new(big.Int).Mul(value.high, next.low), new(big.Int).Mul(value.high, next.high)}
				lo, hi := corners[0], corners[0]
				for _, corner := range corners[1:] {
					if corner.Cmp(lo) < 0 {
						lo = corner
					}
					if corner.Cmp(hi) > 0 {
						hi = corner
					}
				}
				value = limits{lo, hi}
			}
		}
		return value
	}
	panic("unsupported interval term")
}

func integerAlgebra(t airdata.Term) string {
	if t.Kind == "constant" {
		if t.Value == airdata.Modulus-1 {
			return "(-1 : Int)"
		}
		return fmt.Sprintf("(%d : Int)", t.Value)
	}
	if t.Kind == "column" {
		return fmt.Sprintf("(v %d)", t.Column)
	}
	op := map[string]string{"add": " + ", "sub": " - ", "mul": " * "}[t.Kind]
	args := t.Args
	value := "(0 : Int)"
	if t.Kind == "mul" {
		value = "(1 : Int)"
	}
	if t.Kind == "sub" {
		value = integerAlgebra(args[0])
		args = args[1:]
	}
	for _, arg := range args {
		value = "(" + value + op + integerAlgebra(arg) + ")"
	}
	return value
}

func writeIntegerRows(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.Generated.Artifact\nimport DivRemFV.Intervals\nimport Mathlib.Tactic.IntervalCases\n\nset_option maxRecDepth 4096\nset_option maxHeartbeats 4000000\n\nnamespace DivRemFV.Generated\n\n")
	for _, m := range a.Modules {
		if m.Static {
			continue
		}
		bounds := make([]int64, len(m.Columns))
		fmt.Fprintf(&out, "def intervals%d : Array Interval := #[\n", m.ID)
		for i, col := range m.Columns {
			bounds[i] = int64(airdata.Modulus - 1)
			if col.Bits != nil && findRange(a, m.ID, col) != nil {
				bounds[i] = (int64(1) << *col.Bits) - 1
			}
			if i != 0 {
				out.WriteString(",\n")
			}
			fmt.Fprintf(&out, "  ⟨0, %d⟩", bounds[i])
		}
		out.WriteString("\n]\n")
		fmt.Fprintf(&out, "def columns%d (col : Nat) : Interval := intervals%d[col]?.getD ⟨0, %d⟩\n\n", m.ID, m.ID, airdata.Modulus-1)
		fmt.Fprintf(&out, "theorem column_bounds%d (tables : Tables) (row : Nat)\n    (inside : row < (tables %d).size) (accepted : ConstraintsHold tables constraints)\n    (ranges : StaticRanges tables) :\n    ∀ col, (columns%d col).Contains ((readCell tables %d col row).val : Int) := by\n  intro col\n  have bound := (readCell tables %d col row).isLt\n  have nonnegative : (0 : Int) ≤ (readCell tables %d col row).val := by omega\n  by_cases small : col < %d\n  · have bounds := bounds%d tables row inside accepted ranges\n    interval_cases col\n", m.ID, m.ID, m.ID, m.ID, m.ID, m.ID, len(m.Columns), m.ID)
		for index, col := range m.Columns {
			fmt.Fprintf(&out, "    · change (0 : Int) ≤ (readCell tables %d %d row).val ∧\n        ((readCell tables %d %d row).val : Int) ≤ %d\n      constructor\n      · omega\n", m.ID, index, m.ID, index, bounds[index])
			if col.Bits != nil && findRange(a, m.ID, col) != nil {
				fmt.Fprintf(&out, "      · have width := bounds.b%d; omega\n", col.ID)
			} else {
				out.WriteString("      · dsimp [fieldModulus] at bound; omega\n")
			}
		}
		fmt.Fprintf(&out, "  · have missing : intervals%d[col]? = none := by\n      apply Array.getElem?_eq_none\n      simpa [intervals%d] using Nat.le_of_not_gt small\n    simp only [columns%d, missing, Option.getD_none, Interval.Contains]\n    constructor\n    · exact nonnegative\n    · dsimp [fieldModulus] at bound; omega\n\n", m.ID, m.ID, m.ID)
		selected := []airdata.Constraint{}
		for _, c := range a.Constraints {
			if c.Owner != m.ID || c.Kind != "vanishing" {
				continue
			}
			interval := expressionLimits(*c.Expr, bounds)
			if interval.low.Cmp(number(-int64(airdata.Modulus))) > 0 && interval.high.Cmp(number(int64(airdata.Modulus))) < 0 {
				selected = append(selected, c)
			}
		}
		fmt.Fprintf(&out, "structure IntegerEquations%d (v : Nat → Int) : Prop where\n", m.ID)
		for _, c := range selected {
			fmt.Fprintf(&out, "  h%d : %s = 0\n", c.ID, integerAlgebra(*c.Expr))
		}
		fmt.Fprintf(&out, "\ntheorem integer_equations%d (tables : Tables) (row : Nat)\n    (inside : row < (tables %d).size) (accepted : ConstraintsHold tables constraints)\n    (ranges : StaticRanges tables) :\n    IntegerEquations%d (fun col => ((readCell tables %d col row).val : Int)) := by\n  have bounded := column_bounds%d tables row inside accepted ranges\n  constructor\n", m.ID, m.ID, m.ID, m.ID, m.ID)
		for _, c := range selected {
			fmt.Fprintf(&out, "  · have acceptedExpr := accepted c%d member%d\n    have fieldZero := congrArg (fun value : Nat => (value : K))\n      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))\n    have lifted := Expr.lift_row_zero\n      (match c%d with | .vanishing _ _ expr => expr | _ => .constant 0)\n      tables %d row columns%d bounded (by decide)\n      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)\n    simpa [c%d, Expr.evalInteger, integerConstant, fieldModulus] using lifted\n", c.ID, c.ID, c.ID, m.ID, m.ID, c.ID)
		}
		out.WriteString("\n")
	}
	out.WriteString("end DivRemFV.Generated\n")
	writeScoped("IntegerRows", out.String())
}

func findRange(a airdata.Artifact, mid uint, col airdata.Column) *airdata.Constraint {
	for i := range a.Constraints {
		c := &a.Constraints[i]
		if c.Owner != mid {
			continue
		}
		if *col.Bits < 2 {
			if c.Name == fmt.Sprintf("range_u%d_%d#0", *col.Bits, col.ID) {
				return c
			}
		} else if c.Kind == "lookup" && len(c.Sources) == 1 && c.Sources[0].Selector == nil && len(c.Sources[0].Columns) == 1 && c.Sources[0].Columns[0] == col.ID {
			return c
		}
	}
	return nil
}

func check(err error) {
	if err != nil {
		panic(err)
	}
}

func term(t airdata.Term) string {
	switch t.Kind {
	case "constant":
		return fmt.Sprintf("(.constant ⟨%d, by decide⟩)", t.Value)
	case "column":
		return fmt.Sprintf("(.column %d (%d))", t.Column, t.Shift)
	case "add", "mul", "sub":
		args := t.Args
		var acc string
		if t.Kind == "sub" {
			acc = term(args[0])
			args = args[1:]
		} else if t.Kind == "add" {
			acc = "(.constant 0)"
		} else {
			acc = "(.constant 1)"
		}
		for _, arg := range args {
			acc = fmt.Sprintf("(.%s %s %s)", t.Kind, acc, term(arg))
		}
		return acc
	}
	panic("unsupported term")
}

func algebra(t airdata.Term) string {
	switch t.Kind {
	case "constant":
		return fmt.Sprintf("(%d : K)", t.Value)
	case "column":
		if t.Shift != 0 {
			panic("shifted helper expression")
		}
		return fmt.Sprintf("(v %d)", t.Column)
	case "add", "mul", "sub":
		op := map[string]string{"add": " + ", "mul": " * ", "sub": " - "}[t.Kind]
		args := t.Args
		var acc string
		if t.Kind == "sub" {
			acc = algebra(args[0])
			args = args[1:]
		} else if t.Kind == "add" {
			acc = "(0 : K)"
		} else {
			acc = "(1 : K)"
		}
		for _, arg := range args {
			acc = "(" + acc + op + algebra(arg) + ")"
		}
		return acc
	}
	panic("unsupported algebra")
}

func vectors(vs []airdata.Vector) string {
	parts := []string{}
	for _, v := range vs {
		sel := "none"
		if v.Selector != nil {
			sel = fmt.Sprintf("some %d", *v.Selector)
		}
		cols := []string{}
		for _, c := range v.Columns {
			cols = append(cols, fmt.Sprint(c))
		}
		parts = append(parts, fmt.Sprintf("⟨%d, %s, #[%s]⟩", v.Module, sel, strings.Join(cols, ", ")))
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

func constraint(c airdata.Constraint) string {
	switch c.Kind {
	case "vanishing":
		domain := "none"
		if c.Domain != nil {
			domain = fmt.Sprintf("(some (%d))", *c.Domain)
		}
		return fmt.Sprintf(".vanishing %d %s %s", c.Owner, domain, term(*c.Expr))
	case "range":
		return fmt.Sprintf(".range %d %d %d", c.Owner, c.Column, c.Bits)
	case "lookup", "bus":
		return fmt.Sprintf(".%s %s %s", c.Kind, vectors(c.Sources), vectors(c.Targets))
	}
	panic("unsupported constraint")
}
