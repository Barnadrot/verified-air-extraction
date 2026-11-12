package main

import (
	"divremfv/internal/airdata"
	"fmt"

	"strings"
)

func writeReverseRows(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.Generated.IntegerRows\n\nset_option maxRecDepth 4096\n\nnamespace DivRemFV.Generated\n\n")
	for _, m := range a.Modules {
		if m.Static {
			continue
		}
		bounds := make([]int64, len(m.Columns))
		for i, col := range m.Columns {
			bounds[i] = int64(airdata.Modulus - 1)
			if col.Bits != nil && findRange(a, m.ID, col) != nil {
				bounds[i] = (int64(1) << *col.Bits) - 1
			}
		}
		lifted := map[uint]bool{}
		cs := []airdata.Constraint{}
		for _, c := range a.Constraints {
			if c.Owner != m.ID || c.Kind != "vanishing" {
				continue
			}
			cs = append(cs, c)
			interval := expressionLimits(*c.Expr, bounds)
			lifted[c.ID] = interval.low.Cmp(number(-int64(airdata.Modulus))) > 0 && interval.high.Cmp(number(int64(airdata.Modulus))) < 0
		}
		fmt.Fprintf(&out, "theorem integer_to_field%d (v : Nat → Nat)\n    (h : IntegerEquations%d (fun col => (v col : Int)))\n", m.ID, m.ID)
		for _, c := range cs {
			if !lifted[c.ID] {
				fmt.Fprintf(&out, "    (e%d : %s = 0)\n", c.ID, algebra(*c.Expr))
			}
		}
		fmt.Fprintf(&out, "    : Equations%d (fun col => (v col : K)) := by\n  have minusOne : (2130706432 : K) = -1 := by decide\n  constructor\n", m.ID)
		for _, c := range cs {
			if !lifted[c.ID] {
				fmt.Fprintf(&out, "  · exact e%d\n", c.ID)
				continue
			}
			fmt.Fprintf(&out, "  · have cast := congrArg (fun value : Int => (value : K)) h.h%d\n    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,\n      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast\n", c.ID)
		}
		out.WriteString("\n")
	}
	out.WriteString("end DivRemFV.Generated\n")
	writeScoped("ReverseRows", out.String())
}
