package airdata

// EncodeArtifactWire uses the complete grammar in DivRemFV.ArtifactWire.
// JSON is retained for inspection; it is not the proof transport.
func EncodeArtifactWire(a Artifact) ([]byte, error) {
	if a.Format != "divrem-air-v1" || a.Field != "KOALABEAR_16" || a.Modulus != Modulus {
		return nil, captureError("unsupported wire artifact format or field")
	}
	out := appendWireWord(nil, 1146242647)
	out = appendWireWord(out, 1)
	out = appendWireWord(out, Modulus)
	out = appendWireModules(out, a.Modules)
	return appendWireConstraints(out, a.Constraints)
}

func appendWireModule(out []byte, m Module) []byte {
	out = appendWireWord(out, uint64(m.ID))
	out = appendWireName(out, m.Name)
	out = appendWireBool(out, m.Static)
	out = appendWireBool(out, m.Native)
	out = appendWireColumns(out, m.Columns)
	return appendWireRows(out, m.Content)
}

func appendWireModules(out []byte, modules []Module) []byte {
	out = appendWireWord(out, uint64(len(modules)))
	for _, m := range modules {
		out = appendWireModule(out, m)
	}
	return out
}

func appendWireConstraints(out []byte, constraints []Constraint) ([]byte, error) {
	out = appendWireWord(out, uint64(len(constraints)))
	for _, c := range constraints {
		var err error
		out, err = appendWireConstraint(out, c)
		if err != nil {
			return nil, err
		}
	}
	return out, nil
}

func appendWireColumns(out []byte, columns []Column) []byte {
	out = appendWireWord(out, uint64(len(columns)))
	for _, c := range columns {
		out = appendWireColumn(out, c)
	}
	return out
}

func appendWireRows(out []byte, rows [][]uint64) []byte {
	out = appendWireWord(out, uint64(len(rows)))
	for _, row := range rows {
		out = appendWireRow(out, row)
	}
	return out
}

func appendWireRow(out []byte, row []uint64) []byte {
	out = appendWireWord(out, uint64(len(row)))
	for _, value := range row {
		out = appendWireWord(out, value)
	}
	return out
}

func appendWireConstraint(out []byte, c Constraint) ([]byte, error) {
	out = appendWireWord(out, uint64(c.ID))
	out = appendWireWord(out, uint64(c.Owner))
	out = appendWireName(out, c.Name)
	switch c.Kind {
	case "vanishing":
		out = appendWireWord(out, 0)
		out = appendWireWord(out, uint64(c.Owner))
		out = appendWireDomain(out, c.Domain)
		return appendWireFramedTerm(out, *c.Expr)
	case "range":
		out = appendWireWord(appendWireWord(out, 1), 0)
		out = appendWireWord(out, uint64(c.Owner))
		out = appendWireWord(out, uint64(c.Column))
		out = appendWireWord(out, uint64(c.Bits))
	case "lookup", "bus":
		out = appendWireWord(appendWireWord(out, 1), 1)
		if c.Kind == "lookup" {
			out = appendWireWord(out, 0)
		} else {
			out = appendWireWord(out, 1)
		}
		out = appendWirePorts(out, c.Sources)
		out = appendWirePorts(out, c.Targets)
	default:
		return nil, captureError("unsupported wire constraint")
	}
	return out, nil
}

func appendWireDomain(out []byte, domain *int) []byte {
	if domain == nil {
		return appendWireWord(appendWireWord(out, 0), 0)
	}
	out = appendWireWord(out, 1)
	return appendWireWord(out, (uint64(*domain)<<1)^uint64(*domain>>63))
}

func appendWireFramedTerm(out []byte, term Term) ([]byte, error) {
	encoded, err := EncodeTermWire(term)
	if err != nil {
		return nil, err
	}
	out = appendWireWord(out, uint64(len(encoded)/8))
	return append(out, encoded...), nil
}

func appendWireColumn(out []byte, c Column) []byte {
	out = appendWireWord(out, uint64(c.ID))
	out = appendWireName(out, c.Name)
	out = appendWireOption(out, c.Bits)
	out = appendWireBool(out, c.Input)
	out = appendWireBool(out, c.Output)
	return appendWireBool(out, c.Native)
}

func appendWireBool(out []byte, value bool) []byte {
	if value {
		out = appendWireWord(out, 1)
	} else {
		out = appendWireWord(out, 0)
	}
	return appendWireWord(out, 0)
}

func appendWireOption(out []byte, value *uint) []byte {
	if value == nil {
		return appendWireWord(appendWireWord(out, 0), 0)
	}
	return appendWireWord(appendWireWord(out, 1), uint64(*value))
}

func appendWireName(out []byte, value string) []byte {
	out = appendWireWord(out, uint64(len(value)))
	for i := 0; i < len(value); i++ {
		out = appendWireWord(out, uint64(value[i]))
	}
	return out
}

func appendWirePorts(out []byte, ports []Vector) []byte {
	out = appendWireWord(out, uint64(len(ports)))
	for _, p := range ports {
		out = appendWirePort(out, p)
	}
	return out
}

func appendWirePort(out []byte, p Vector) []byte {
	out = appendWireWord(out, uint64(p.Module))
	out = appendWireOption(out, p.Selector)
	out = appendWireWord(out, uint64(len(p.Columns)))
	for _, col := range p.Columns {
		out = appendWireWord(out, uint64(col))
	}
	return out
}
