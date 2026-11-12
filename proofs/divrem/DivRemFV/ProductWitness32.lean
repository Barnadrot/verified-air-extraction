import DivRemFV.Unsigned32
import Mathlib.Tactic.Ring

namespace DivRemFV

def digit15 (value index : Nat) : Nat := value / 32768 ^ index % 32768

def partial32 (a b i j : Nat) : Nat :=
  (if i = 2 then a / 1073741824 else digit15 a i) *
  (if j = 2 then b / 1073741824 else digit15 b j)

def middle32 (a b : Nat) : Nat :=
  partial32 a b 0 0 / 32768 + partial32 a b 0 1 % 32768 + partial32 a b 1 0 % 32768

def next32 (a b : Nat) : Nat :=
  partial32 a b 0 1 / 32768 + partial32 a b 0 2 % 32768 +
  partial32 a b 1 0 / 32768 + partial32 a b 1 1 % 32768 + partial32 a b 2 0 % 32768

def overflowLow32 (a b : Nat) : Nat :=
  partial32 a b 0 2 / 32768 + partial32 a b 1 1 / 32768 +
  partial32 a b 1 2 % 32768 + partial32 a b 2 0 / 32768 + partial32 a b 2 1 % 32768

def overflowHigh32 (a b : Nat) : Nat :=
  partial32 a b 1 2 / 32768 + partial32 a b 2 1 / 32768 + partial32 a b 2 2

theorem split15_32 (value : Nat) :
    value = value % 32768 + 32768 * (value / 32768 % 32768) + 1073741824 * (value / 1073741824) := by
  have first := Nat.mod_add_div value 32768
  have second := Nat.mod_add_div (value / 32768) 32768
  rw [Nat.div_div_eq_div_mul] at second
  norm_num only [show 32768 * 32768 = 1073741824 by decide] at second
  omega

theorem product32_expansion (a b : Nat) :
    a * b = partial32 a b 0 0 % 32768 + 32768 * middle32 a b +
      1073741824 * next32 a b + 35184372088832 * overflowLow32 a b +
      1152921504606846976 * overflowHigh32 a b := by
  have first := split15_32 a
  have second := split15_32 b
  have expansion : a * b =
      partial32 a b 0 0 +
      32768 * (partial32 a b 0 1 + partial32 a b 1 0) +
      1073741824 * (partial32 a b 0 2 + partial32 a b 1 1 + partial32 a b 2 0) +
      35184372088832 * (partial32 a b 1 2 + partial32 a b 2 1) +
      1152921504606846976 * partial32 a b 2 2 := by
    calc
      a * b = (a % 32768 + 32768 * (a / 32768 % 32768) + 1073741824 * (a / 1073741824)) *
        (b % 32768 + 32768 * (b / 32768 % 32768) + 1073741824 * (b / 1073741824)) :=
          congrArg₂ (· * ·) first second
      _ = _ := by norm_num [partial32, digit15]; ring
  rw [expansion]
  have p00 := Nat.mod_add_div (partial32 a b 0 0) 32768
  have p01 := Nat.mod_add_div (partial32 a b 0 1) 32768
  have p02 := Nat.mod_add_div (partial32 a b 0 2) 32768
  have p10 := Nat.mod_add_div (partial32 a b 1 0) 32768
  have p11 := Nat.mod_add_div (partial32 a b 1 1) 32768
  have p12 := Nat.mod_add_div (partial32 a b 1 2) 32768
  have p20 := Nat.mod_add_div (partial32 a b 2 0) 32768
  have p21 := Nat.mod_add_div (partial32 a b 2 1) 32768
  unfold middle32 next32 overflowLow32 overflowHigh32
  omega

theorem product32_no_overflow (a b : Nat) (bounded : a * b < 4294967296) :
    overflowLow32 a b = 0 ∧ overflowHigh32 a b = 0 := by
  have expansion := product32_expansion a b
  clear * - bounded expansion
  omega

theorem partial32_bound (a b i j : Nat) (aBound : a < 4294967296) (bBound : b < 4294967296) :
    partial32 a b i j < 1073741824 := by
  have aPart : (if i = 2 then a / 1073741824 else digit15 a i) < 32768 := by
    split_ifs
    · omega
    · exact Nat.mod_lt _ (by decide)
  have bPart : (if j = 2 then b / 1073741824 else digit15 b j) < 32768 := by
    split_ifs
    · omega
    · exact Nat.mod_lt _ (by decide)
  unfold partial32
  have aCap : (if i = 2 then a / 1073741824 else digit15 a i) ≤ 32767 := by omega
  have bCap : (if j = 2 then b / 1073741824 else digit15 b j) ≤ 32767 := by omega
  exact lt_of_le_of_lt (Nat.mul_le_mul aCap bCap) (by decide)

theorem product32_middle_bound (a b : Nat) (aBound : a < 4294967296) (bBound : b < 4294967296) :
    middle32 a b < 98304 := by
  have product := partial32_bound a b 0 0 aBound bBound
  unfold middle32
  omega

theorem product32_merge (a b : Nat) (bounded : a * b < 4294967296) :
    let middle := middle32 a b
    let high := next32 a b + middle / 32768
    high < 4 ∧
    a * b % 65536 = partial32 a b 0 0 % 32768 + 32768 * (middle % 32768 % 2) ∧
    a * b / 65536 = middle % 32768 / 2 + 16384 * high := by
  have expansion := product32_expansion a b
  obtain ⟨lowZero,highZero⟩ := product32_no_overflow a b bounded
  rw [lowZero,highZero] at expansion
  simp only [mul_zero,add_zero] at expansion
  dsimp
  omega

end DivRemFV

