package airdata

// EncodeTermWire emits the prefix grammar in DivRemFV.TermWire. Each token is
// an unsigned 64-bit little-endian word. This writer still needs a source proof.
func EncodeTermWire(t Term) ([]byte, error) {
	return appendTermWire(nil, t)
}

func appendWireWord(out []byte, value uint64) []byte {
	return append(out, byte(value), byte(value>>8), byte(value>>16), byte(value>>24),
		byte(value>>32), byte(value>>40), byte(value>>48), byte(value>>56))
}

func appendArgsWire(out []byte, args []Term) ([]byte, error) {
	for _, arg := range args {
		out = appendWireWord(out, 1)
		var err error
		out, err = appendTermWire(out, arg)
		if err != nil {
			return nil, err
		}
	}
	return appendWireWord(out, 0), nil
}

func appendTermWire(out []byte, t Term) ([]byte, error) {
	switch t.Kind {
	case "constant":
		if t.Value >= Modulus || len(t.Args) != 0 {
			return nil, captureError("invalid wire constant")
		}
		return appendWireWord(appendWireWord(out, 0), t.Value), nil
	case "column":
		if len(t.Args) != 0 {
			return nil, captureError("wire column has arguments")
		}
		shift := (uint64(t.Shift) << 1) ^ uint64(t.Shift>>63)
		return appendWireWord(appendWireWord(appendWireWord(out, 1), uint64(t.Column)), shift), nil
	case "add":
		return appendArgsWire(appendWireWord(out, 2), t.Args)
	case "sub":
		if len(t.Args) == 0 {
			return nil, captureError("empty wire subtraction")
		}
		out, err := appendTermWire(appendWireWord(out, 3), t.Args[0])
		if err != nil {
			return nil, err
		}
		return appendArgsWire(out, t.Args[1:])
	case "mul":
		return appendArgsWire(appendWireWord(out, 4), t.Args)
	default:
		return nil, captureError("unsupported wire term")
	}
}
