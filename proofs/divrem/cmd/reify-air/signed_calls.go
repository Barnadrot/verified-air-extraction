package main

import (
	"fmt"
	"math/big"
	"os"
	"strings"

	"divremfv/internal/airdata"
)

func writeSignedCalls(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.Generated.Calls\nimport DivRemFV.AbsoluteValue\nimport DivRemFV.Negation\nimport DivRemFV.SignedSpec\n\nnamespace DivRemFV\nopen Generated\n\n")
	for _, n := range []int{2, 4} {
		width, mid, absMid, uMid, negMid, ret, qa, ra, magA, magB, qSel, rSel := 32, 64, 56, 63, 66, 23, 8, 10, 13, 15, 24, 25
		pack := func(start int) string { return fmt.Sprintf("pairValue v %d %d", start, start+1) }
		if n == 4 {
			width = 64
			mid = 62
			absMid = 55
			uMid = 61
			negMid = 65
			ret = 43
			qa = 16
			ra = 20
			magA = 25
			magB = 29
			qSel = 44
			rSel = 45
			pack = func(start int) string { return fmt.Sprintf("wordValue v %d", start) }
		}
		fmt.Fprintf(&out, "structure SignedCalls%d (v : Nat → Nat) : Prop where\n  absoluteA : %s = magnitudeNat %d (%s)\n  absoluteB : %s = magnitudeNat %d (%s)\n  quotient : %s = (if %s = 0 then %s else %s / %s)\n  remainder : %s = (if %s = 0 then %s else %s %% %s)\n  negativeQ : v %d ≠ 0 → %s = negateNat %d (%s)\n  negativeR : v %d ≠ 0 → %s = negateNat %d (%s)\n\n", width, pack(magA), width, pack(0), pack(magB), width, pack(n), pack(qa), pack(magB), newMaxWord(width), pack(magA), pack(magB), pack(ra), pack(magB), pack(magA), pack(magA), pack(magB), qSel, pack(2*n), width, pack(qa), rSel, pack(3*n), width, pack(ra))
		calls := map[string]airdata.Constraint{}
		for _, c := range a.Constraints {
			if c.Owner != uint(mid) || c.Kind != "lookup" || len(c.Targets) != 1 || len(c.Sources) != 1 {
				continue
			}
			s, t := c.Sources[0], c.Targets[0]
			if t.Module == uint(absMid) && s.Columns[0] == 0 {
				calls["absoluteA"] = c
			}
			if t.Module == uint(absMid) && s.Columns[0] == uint(n) {
				calls["absoluteB"] = c
			}
			if t.Module == uint(uMid) {
				calls["unsigned"] = c
			}
			if t.Module == uint(negMid) && s.Columns[0] == uint(qa) {
				calls["negativeQ"] = c
			}
			if t.Module == uint(negMid) && s.Columns[0] == uint(ra) {
				calls["negativeR"] = c
			}
		}
		if len(calls) != 5 {
			panic("signed helper call closure changed")
		}
		fmt.Fprintf(&out, "theorem signed_calls%d_of_ranges (tables : Tables) (row : Nat)\n    (inside : row < (tables %d).size) (accepted : ConstraintsHold tables constraints)\n    (ranges : StaticRanges tables) (active : readCell tables %d %d row ≠ 0) :\n    SignedCalls%d (fun col => (readCell tables %d col row).val) := by\n", width, mid, mid, ret, width, mid)
		out.WriteString("  constructor\n")
		for _, label := range []string{"absoluteA", "absoluteB", "quotient", "remainder"} {
			callLabel := label
			if label == "quotient" || label == "remainder" {
				callLabel = "unsigned"
			}
			c := calls[callLabel]
			names := bindingNames(len(c.Sources[0].Columns))
			fmt.Fprintf(&out, "  · obtain ⟨callee, inCallee, selected, %s⟩ := call%d tables row inside accepted active\n", strings.Join(names, ","), c.ID)
			helper := fmt.Sprintf("absolute%d_air_sound_of_ranges", width)
			args := "ranges selected"
			if callLabel == "unsigned" {
				helper = fmt.Sprintf("unsigned%d_air_sound", width)
				if width == 64 {
					helper += "_of_ranges"
				}
			}
			part := ""
			if label == "quotient" {
				part = ".1"
			}
			if label == "remainder" {
				part = ".2"
			}
			fmt.Fprintf(&out, "    have result := %s tables callee inCallee accepted %s\n    simpa only [magnitudeNat, pairValue, wordValue, %s] using result%s\n", helper, args, strings.Join(names, ", "), part)
		}
		for _, label := range []string{"negativeQ", "negativeR"} {
			c := calls[label]
			names := bindingNames(len(c.Sources[0].Columns))
			sel := *c.Sources[0].Selector
			fmt.Fprintf(&out, "  · intro enabled\n    have sourceActive : readCell tables %d %d row ≠ 0 := by\n      intro zero\n      exact enabled (congrArg Fin.val zero)\n    obtain ⟨callee, inCallee, selected, %s⟩ := call%d tables row inside accepted sourceActive\n    have result := negative%d_air_sound_of_ranges tables callee inCallee accepted ranges selected\n    simpa [negateNat, pairValue, wordValue, %s] using result\n", mid, sel, strings.Join(names, ","), c.ID, width, strings.Join(names, ", "))
		}
		fmt.Fprintf(&out, "\ntheorem signed_calls%d (tables : Tables) (row : Nat)\n    (inside : row < (tables %d).size) (accepted : ConstraintsHold tables constraints)\n    (fixed : StaticTablesFixed tables) (active : readCell tables %d %d row ≠ 0) :\n    SignedCalls%d (fun col => (readCell tables %d col row).val) := by\n  exact signed_calls%d_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active\n\n", width, mid, mid, ret, width, mid, width)
	}
	out.WriteString("end DivRemFV\n")
	check(os.WriteFile("DivRemFV/SignedCalls.lean", []byte(out.String()), 0644))
}

func bindingNames(count int) []string {
	names := []string{}
	for i := 0; i < count; i++ {
		names = append(names, fmt.Sprintf("h%d", i))
	}
	return names
}
func newMaxWord(width int) string {
	v := new(big.Int)
	v.SetString(powerOfTwo(width), 10)
	return v.Sub(v, number(1)).String()
}
