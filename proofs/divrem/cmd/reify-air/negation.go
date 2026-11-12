package main

import (
	"fmt"
	"os"
	"strings"

	"divremfv/internal/airdata"
)

func writeNegation(a airdata.Artifact) {
	var out strings.Builder
	out.WriteString("import DivRemFV.Unsigned64Result\n\nnamespace DivRemFV\nopen Generated\n\n")
	for _, n := range []int{2, 4} {
		mid, width, pack, modulus := 66, 32, "pairValue v 0 1", "4294967296"
		outpack := "pairValue v 2 3"
		moduleName := "negative_of_word"
		if n == 4 {
			mid = 65
			width = 64
			pack = "wordValue v 0"
			outpack = "wordValue v 4"
			modulus = "18446744073709551616"
			moduleName = "negative_of_double_word"
		}
		inst := map[int]uint{}
		found := false
		for _, m := range a.Modules {
			if m.ID == uint(mid) && m.Name == moduleName {
				found = true
			}
		}
		if !found {
			panic("negation module mapping changed")
		}
		for _, c := range a.Constraints {
			if c.Owner == uint(mid) {
				var index int
				if _, err := fmt.Sscanf(c.Name, "inst#%d", &index); err == nil {
					inst[index] = c.ID
				}
			}
		}
		ret, flag, sign := 7*n, 5*n+1, 2*n
		guard0 := n + 1
		first0 := n + 2
		guard1 := 3*n + 2
		first1 := guard1 + 1
		fmt.Fprintf(&out, "theorem negative%d_nonzero_arithmetic (v : Nat → Nat) (bounds : Bounds%d v)\n    (h : IntegerEquations%d (fun col => (v col : Int)))\n    (active : v %d = 1) (nonzero : v %d = 1) :\n    %s + %s = %s := by\n  have bit := bounds.b%d\n  have cases : v %d = 0 ∨ v %d = 1 := by clear * - bit; omega\n  have ret : (v %d : Int) = 1 := by simp [active]\n  have flag : (v %d : Int) = 1 := by simp [nonzero]\n  rcases cases with positive | negative\n", width, mid, mid, ret, flag, outpack, pack, modulus, sign, sign, sign, ret, flag)
		for branch := 0; branch < 2; branch++ {
			label := []string{"positive", "negative"}[branch]
			guard, first, start := guard0, first0, 2*n+1
			if branch == 1 {
				guard = guard1
				first = first1
				start = 3*n + 1
			}
			fmt.Fprintf(&out, "  · have sign : (v %d : Int) = %d := by simp [%s]\n    have guard := h.h%d\n", sign, branch, label, inst[guard])
			for i := 0; i < 2*n; i++ {
				fmt.Fprintf(&out, "    have e%d := h.h%d\n", i, inst[first+i])
			}
			out.WriteString("    simp only [ret, flag, sign, one_mul, mul_one, zero_add, sub_zero, neg_mul] at guard")
			for i := 0; i < 2*n; i++ {
				fmt.Fprintf(&out, " e%d", i)
			}
			out.WriteString("\n")
			for i := 0; i < n; i++ {
				fmt.Fprintf(&out, "    have cap%d := bounds.b%d\n", i, start+i)
			}
			for i := 0; i < n; i++ {
				fmt.Fprintf(&out, "    have full%d : v %d = 65535 := by\n      clear * - guard", i, start+i)
				for j := 0; j < n; j++ {
					fmt.Fprintf(&out, " cap%d", j)
				}
				out.WriteString("\n      omega\n")
			}
			fmt.Fprintf(&out, "    have identity : (%s : Int) + (%s : Int) = %s := by\n      simp only [pairValue, wordValue, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]\n      simp only [", outpack, pack, modulus)
			fullNames := []string{}
			for i := 0; i < n; i++ {
				fullNames = append(fullNames, fmt.Sprintf("full%d", i))
			}
			out.WriteString(strings.Join(fullNames, ", ") + "] at")
			for i := 0; i < 2*n; i++ {
				fmt.Fprintf(&out, " e%d", i)
			}
			out.WriteString("\n      linear_combination ")
			terms := []string{}
			for i := 0; i < 2*n; i++ {
				coefficient := newCoefficient(i%n, 16)
				if branch == 0 && i > 0 && i < n {
					coefficient = "-" + coefficient
				}
				terms = append(terms, fmt.Sprintf("(%s) * e%d", coefficient, i))
			}
			out.WriteString(strings.Join(terms, " + ") + "\n    exact_mod_cast identity\n")
		}
		fmt.Fprintf(&out, "\ntheorem negative%d_result (v : Nat → Nat) (bounds : Bounds%d v)\n    (fieldEquations : Equations%d (fun col => (v col : K)))\n    (integerEquations : IntegerEquations%d (fun col => (v col : Int)))\n    (active : v %d ≠ 0) :\n    %s = (if %s = 0 then 0 else %s - %s) := by\n  have br := bounds.b%d\n  have bf := bounds.b%d\n  have activeOne : v %d = 1 := by clear * - br active; omega\n  have cases : v %d = 0 ∨ v %d = 1 := by clear * - bf; omega\n  rcases cases with flagZero | flagOne\n  · have ret : (v %d : Int) = 1 := by simp [activeOne]\n    have flag : (v %d : Int) = 0 := by simp [flagZero]\n    have guard := integerEquations.h%d\n    simp only [ret, flag, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero, sub_zero] at guard\n    have zeros : %s = 0 ∧ %s = 0 := by\n      dsimp [pairValue, wordValue]\n      clear * - guard\n      omega\n    simp [zeros.1, zeros.2]\n  · have positive : 0 < %s := by\n      by_contra failure\n", width, mid, mid, mid, ret, outpack, pack, modulus, pack, ret, flag, ret, flag, flag, ret, flag, inst[guard0], outpack, pack, pack)
		zeroTerms := []string{}
		zeroNames := []string{}
		for i := 0; i < n; i++ {
			zeroTerms = append(zeroTerms, fmt.Sprintf("v %d = 0", i))
			zeroNames = append(zeroNames, fmt.Sprintf("z%d", i))
		}
		fmt.Fprintf(&out, "      have zeros : %s := by\n        dsimp [pairValue, wordValue] at failure\n        clear * - failure\n        omega\n      rcases zeros with ⟨%s⟩\n      have check := fieldEquations.h%d\n      norm_num [activeOne, flagOne, %s] at check\n    have identity := negative%d_nonzero_arithmetic v bounds integerEquations activeOne flagOne\n    rw [if_neg (Nat.ne_of_gt positive)]\n    clear * - identity\n    omega\n", strings.Join(zeroTerms, " ∧ "), strings.Join(zeroNames, ","), inst[n], strings.Join(zeroNames, ", "), width)
		fmt.Fprintf(&out, "\ntheorem negative%d_air_sound_of_ranges (tables : Tables) (row : Nat)\n    (inside : row < (tables %d).size) (accepted : ConstraintsHold tables constraints)\n    (ranges : StaticRanges tables) (active : readCell tables %d %d row ≠ 0) :\n    let v := fun col => (readCell tables %d col row).val\n    %s = (if %s = 0 then 0 else %s - %s) := by\n  apply negative%d_result _ (bounds%d tables row inside accepted ranges)\n    (equations%d tables row inside accepted) (integer_equations%d tables row inside accepted ranges)\n  intro zero\n  exact active (Fin.ext zero)\n\n", width, mid, mid, ret, mid, outpack, pack, modulus, pack, width, mid, mid, mid)
		fmt.Fprintf(&out, "theorem negative%d_air_sound (tables : Tables) (row : Nat)\n    (inside : row < (tables %d).size) (accepted : ConstraintsHold tables constraints)\n    (fixed : StaticTablesFixed tables) (active : readCell tables %d %d row ≠ 0) :\n    let v := fun col => (readCell tables %d col row).val\n    %s = (if %s = 0 then 0 else %s - %s) := by\n  exact negative%d_air_sound_of_ranges tables row inside accepted (fixed_tables_have_ranges tables fixed) active\n\n", width, mid, mid, ret, mid, outpack, pack, modulus, pack, width)
	}
	out.WriteString("end DivRemFV\n")
	check(os.WriteFile("DivRemFV/Negation.lean", []byte(out.String()), 0644))
}

func newCoefficient(exponent, baseBits int) string { return powerOfTwo(exponent * baseBits) }
