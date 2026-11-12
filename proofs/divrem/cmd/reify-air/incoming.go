package main

import (
	"divremfv/internal/airdata"
	"encoding/json"
	"fmt"
	"os"
	"strings"
)

func writeIncoming() {
	data, err := os.ReadFile("artifacts/helper-interfaces.json")
	check(err)
	var calls []airdata.Constraint
	check(json.Unmarshal(data, &calls))
	var out strings.Builder
	out.WriteString("import DivRemFV.Air\n\nnamespace DivRemFV.Generated\n\n")
	for _, c := range calls {
		if c.Kind != "lookup" || len(c.Sources) != 1 || len(c.Targets) != 1 {
			panic("unsupported incoming call")
		}
		fmt.Fprintf(&out, "def incoming%d : Constraint := %s\n", c.ID, constraint(c))
	}
	out.WriteString("\ndef incomingConstraints : List Constraint := [")
	for index, c := range calls {
		if index > 0 {
			out.WriteString(",")
		}
		fmt.Fprintf(&out, "incoming%d", c.ID)
	}
	out.WriteString("]\n")
	out.WriteString("\ndef callTarget (call : Constraint) : Port :=\n  match call with\n  | .lookup _ [target] => target\n  | _ => ⟨0,none,#[]⟩\n\nend DivRemFV.Generated\n")
	check(os.WriteFile("DivRemFV/Generated/Incoming.lean", []byte(out.String()), 0644))
}
