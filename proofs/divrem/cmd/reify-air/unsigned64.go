package main

import (
	"fmt"
	"math/big"
	"os"
	"strings"

	"divremfv/internal/airdata"
)

func writeUnsigned64(a airdata.Artifact) {
	var module airdata.Module
	for _, m := range a.Modules {
		if m.Name == "divMod_64_uu" {
			module = m
		}
	}
	if module.ID != 61 || len(module.Columns) != 123 {
		panic("unsigned64 layout requires a checked mapping")
	}
	inst := map[int]uint{}
	var zeroID uint
	for _, c := range a.Constraints {
		if c.Owner != module.ID {
			continue
		}
		var index int
		if _, err := fmt.Sscanf(c.Name, "inst#%d", &index); err == nil {
			inst[index] = c.ID
		}
		if c.Name == "range_u0_32#0" {
			zeroID = c.ID
		}
	}
	if len(inst) != 70 || zeroID == 0 {
		panic("unsigned64 arithmetic shape changed")
	}
	var out strings.Builder
	out.WriteString("import DivRemFV.Generated.IntegerRows\nimport DivRemFV.Unsigned32\n\nset_option maxHeartbeats 2000000\n\nnamespace DivRemFV\nopen Generated\n\ndef wordInteger (v : Nat → Int) (start : Nat) : Int :=\n  281474976710656 * v start + 4294967296 * v (start + 1) +\n    65536 * v (start + 2) + v (start + 3)\n\ntheorem unsigned64_nonzero_integer (v : Nat → Int)\n    (h : IntegerEquations61 v) (nonnegative : ∀ col, 0 ≤ v col)\n    (active : v 121 = 1) (nonzero : v 33 = 1) :\n    wordInteger v 0 = wordInteger v 4 * wordInteger v 8 + wordInteger v 12 ∧\n    wordInteger v 4 = wordInteger v 12 + wordInteger v 16 + 1 := by\n")
	fmt.Fprintf(&out, "  have zeroEquation := h.h%d\n  have zero : v 32 = 0 := by clear * - zeroEquation; omega\n", zeroID)
	for i := 6; i < 70; i++ {
		fmt.Fprintf(&out, "  have e%d := h.h%d\n", i, inst[i])
	}
	out.WriteString("  simp only [active, nonzero, zero, zero_add, one_mul, mul_one, sub_zero, neg_mul] at")
	for i := 6; i < 70; i++ {
		fmt.Fprintf(&out, " e%d", i)
	}
	out.WriteString("\n")
	qsplit := []int{6, 7, 8, 9, 10, 11, 12}
	bsplit := []int{13, 14, 15, 16, 17, 18, 19}
	for _, split := range []struct {
		name      string
		start     int
		digits    []int
		equations []int
	}{{"qsplit", 8, []int{34, 42, 43, 44, 41}, qsplit}, {"bsplit", 4, []int{45, 53, 54, 55, 52}, bsplit}} {
		fmt.Fprintf(&out, "  have %s : wordInteger v %d = %s := by\n    dsimp [wordInteger]\n    clear * -", split.name, split.start, digitsExpression(split.digits))
		for _, i := range split.equations {
			fmt.Fprintf(&out, " e%d", i)
		}
		out.WriteString("\n    omega\n")
	}
	qdigits := []int{34, 42, 43, 44, 41}
	bdigits := []int{45, 53, 54, 55, 52}
	for i := 0; i < 25; i++ {
		lhs := fmt.Sprintf("v %d + 32768 * v %d", 56+2*i, 57+2*i)
		if i == 24 {
			lhs = "v 104"
		}
		fmt.Fprintf(&out, "  have p%d : %s = v %d * v %d := sub_eq_zero.mp e%d\n", i, lhs, qdigits[i/5], bdigits[i%5], 20+i)
	}
	overflow := []int{65, 73, 74, 81, 82, 89, 90, 97, 98, 75, 83, 84, 91, 92, 99, 100, 85, 93, 94, 101, 102, 95, 103, 104}
	signs := []string{}
	zeros := []string{}
	proofs := []string{}
	names := []string{}
	for _, col := range overflow {
		signs = append(signs, fmt.Sprintf("0 ≤ v %d", col))
		zeros = append(zeros, fmt.Sprintf("v %d = 0", col))
		proofs = append(proofs, fmt.Sprintf("nonnegative %d", col))
		names = append(names, fmt.Sprintf("z%d", col))
	}
	fmt.Fprintf(&out, "  have signs : %s := ⟨%s⟩\n  have zeros : %s := by\n    clear * - signs e49\n    omega\n  rcases zeros with ⟨%s⟩\n", strings.Join(signs, " ∧ "), strings.Join(proofs, ", "), strings.Join(zeros, " ∧ "), strings.Join(names, ","))
	lowGroups := [][]int{{56}, {57, 58, 66}, {59, 60, 67, 68, 76}, {61, 62, 69, 70, 77, 78, 86}, {63, 64, 71, 72, 79, 80, 87, 88, 96}}
	lowTerms := []string{}
	for d, cols := range lowGroups {
		cells := []string{}
		for _, col := range cols {
			cells = append(cells, fmt.Sprintf("v %d", col))
		}
		lowTerms = append(lowTerms, power15(d)+" * ("+strings.Join(cells, " + ")+")")
	}
	low := strings.Join(lowTerms, " + ")
	rawTerms := []string{}
	for i, q := range qdigits {
		for j, b := range bdigits {
			rawTerms = append(rawTerms, fmt.Sprintf("%s * (v %d * v %d)", power15(i+j), q, b))
		}
	}
	fmt.Fprintf(&out, "  have expanded : wordInteger v 8 * wordInteger v 4 =\n      %s := by\n    rw [qsplit, bsplit]\n    calc\n      _ = %s := by ring\n      _ = _ := by\n        rw [", low, strings.Join(rawTerms, " + "))
	parts := []string{}
	for i := 0; i < 25; i++ {
		parts = append(parts, fmt.Sprintf("← p%d", i))
	}
	out.WriteString(strings.Join(parts, ", ") + "]\n")
	fmt.Fprintf(&out, "        simp only [%s, mul_zero, add_zero, zero_add]\n        ring\n", strings.Join(names, ", "))
	out.WriteString("  have product : wordInteger v 8 * wordInteger v 4 = wordInteger v 20 := by\n    dsimp [wordInteger] at expanded ⊢\n    linear_combination expanded")
	for i := 0; i < 4; i++ {
		fmt.Fprintf(&out, " - %s * e%d", power15(i+1), 45+i)
	}
	weights := []string{"1", "65536", "4294967296", "281474976710656"}
	for i, w := range weights {
		fmt.Fprintf(&out, " - %s * e%d", w, 50+i)
	}
	out.WriteString("\n")
	out.WriteString("  have added : wordInteger v 0 = wordInteger v 20 + wordInteger v 12 := by\n    dsimp [wordInteger]\n    linear_combination ")
	terms := []string{}
	for i, w := range weights {
		terms = append(terms, fmt.Sprintf("%s * e%d", w, 54+i), fmt.Sprintf("%s * e%d", w, 58+i))
	}
	out.WriteString(strings.Join(terms, " + ") + "\n")
	out.WriteString("  constructor\n  · rw [← product] at added\n    simpa only [mul_comm] using added\n  · dsimp [wordInteger]\n    linear_combination ")
	terms = []string{}
	for i, w := range weights {
		terms = append(terms, fmt.Sprintf("%s * e%d", w, 62+i), fmt.Sprintf("%s * e%d", w, 66+i))
	}
	out.WriteString(strings.Join(terms, " + ") + "\n\nend DivRemFV\n")
	check(os.WriteFile("DivRemFV/Unsigned64.lean", []byte(out.String()), 0644))
}

func power15(exponent int) string {
	return new(big.Int).Exp(number(32768), number(int64(exponent)), nil).String()
}

func powerOfTwo(exponent int) string { return new(big.Int).Lsh(number(1), uint(exponent)).String() }
func digitsExpression(digits []int) string {
	terms := []string{}
	for i, digit := range digits {
		terms = append(terms, fmt.Sprintf("%s * v %d", power15(i), digit))
	}
	return strings.Join(terms, " + ")
}
