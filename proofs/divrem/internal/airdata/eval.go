package airdata

import "fmt"

type Evaluation struct {
	Row   int    `json:"row"`
	Value uint64 `json:"value"`
}

type ExpressionVector struct {
	Expr     Term         `json:"expr"`
	Rows     [][]uint64   `json:"rows"`
	Expected []Evaluation `json:"expected"`
}

type ExpressionVectors struct {
	Format string             `json:"format"`
	Cases  []ExpressionVector `json:"cases"`
}

func (t Term) HasShift() bool {
	if t.Kind == "column" && t.Shift != 0 {
		return true
	}
	for _, arg := range t.Args {
		if arg.HasShift() {
			return true
		}
	}
	return false
}

// Eval evaluates an exported expression over canonical field values. Values
// beyond the trace boundary are zero, matching ZkC register access evaluation.
func (t Term) Eval(rows [][]uint64, row int) (uint64, error) {
	switch t.Kind {
	case "constant":
		if t.Value >= Modulus {
			return 0, fmt.Errorf("noncanonical constant")
		}
		return t.Value, nil
	case "column":
		r := row + t.Shift
		if r < 0 || r >= len(rows) {
			return 0, nil
		}
		if t.Column >= uint(len(rows[r])) {
			return 0, fmt.Errorf("column out of bounds")
		}
		value := rows[r][t.Column]
		if value >= Modulus {
			return 0, fmt.Errorf("noncanonical cell")
		}
		return value, nil
	case "add", "sub", "mul":
		var value uint64
		start := 0
		if t.Kind == "mul" {
			value = 1
		}
		if t.Kind == "sub" {
			if len(t.Args) == 0 {
				return 0, fmt.Errorf("empty subtraction")
			}
			var err error
			value, err = t.Args[0].Eval(rows, row)
			if err != nil {
				return 0, err
			}
			start = 1
		}
		for _, arg := range t.Args[start:] {
			next, err := arg.Eval(rows, row)
			if err != nil {
				return 0, err
			}
			switch t.Kind {
			case "add":
				value = (value + next) % Modulus
			case "sub":
				value = (value + Modulus - next) % Modulus
			case "mul":
				value = value * next % Modulus
			}
		}
		return value, nil
	default:
		return 0, fmt.Errorf("unsupported term %q", t.Kind)
	}
}
