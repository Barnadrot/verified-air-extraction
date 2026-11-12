package main

import (
	"divremfv/internal/airdata"
	"fmt"
	"strings"
)

func nativeArgs(args []airdata.Term) string {
	out := ".nil"
	for i := len(args) - 1; i >= 0; i-- {
		out = fmt.Sprintf("(.cons %s %s)", nativeTerm(args[i]), out)
	}
	return out
}

func nativeTerm(t airdata.Term) string {
	switch t.Kind {
	case "constant":
		return fmt.Sprintf("(.constant ⟨%d,by decide⟩)", t.Value)
	case "column":
		return fmt.Sprintf("(.column %d (%d))", t.Column, t.Shift)
	case "add":
		return fmt.Sprintf("(.sum %s)", nativeArgs(t.Args))
	case "mul":
		return fmt.Sprintf("(.product %s)", nativeArgs(t.Args))
	case "sub":
		if len(t.Args) == 0 {
			panic("empty subtraction")
		}
		return fmt.Sprintf("(.difference %s %s)", nativeTerm(t.Args[0]), nativeArgs(t.Args[1:]))
	}
	panic("unsupported native term")
}

func nativeConstraint(c airdata.Constraint) string {
	if c.Kind != "vanishing" {
		return constraint(c)
	}
	domain := "none"
	if c.Domain != nil {
		domain = fmt.Sprintf("(some (%d))", *c.Domain)
	}
	return fmt.Sprintf(".vanishing %d %s %s", c.Owner, domain, nativeTerm(*c.Expr))
}

func writeNativeData(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.NativeImport\nimport DivRemFV.Generated.Artifact\n\nset_option maxRecDepth 8192\nset_option maxHeartbeats 4000000\n\nnamespace DivRemFV.Generated.NativeData\nopen DivRemFV.NativeImport\n\n")
	for _, c := range a.Constraints {
		fmt.Fprintf(&out, "def n%d : RawConstraint := %s\n", c.ID, nativeConstraint(c))
	}
	out.WriteString("\ndef rawConstraints : List RawConstraint := [\n")
	for i, c := range a.Constraints {
		if i > 0 {
			out.WriteString(",\n")
		}
		fmt.Fprintf(&out, "  n%d", c.ID)
	}
	out.WriteString("]\n\ntheorem translated_constraints : rawConstraints.map RawConstraint.translate = DivRemFV.Generated.constraints := by rfl\n\ntheorem native_constraints_iff (tables : Tables) :\n    RawConstraintsHold tables rawConstraints ↔ ConstraintsHold tables DivRemFV.Generated.constraints := by\n  rw [← translated_constraints]\n  exact (translate_constraints_holds tables rawConstraints).symm\n\nend DivRemFV.Generated.NativeData\n")
	writeScoped("NativeData", out.String())
}
