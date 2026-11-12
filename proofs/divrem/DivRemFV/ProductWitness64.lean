import DivRemFV.ProductWitness32

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV

def partial64 (a b i j : Nat) : Nat :=
  (if i = 4 then a / 1152921504606846976 else digit15 a i) *
  (if j = 4 then b / 1152921504606846976 else digit15 b j)

def coefficient64 (a b index : Nat) : Nat :=
  match index with
  | 0 => partial64 a b 0 0 % 32768
  | 1 => partial64 a b 0 0 / 32768 + partial64 a b 0 1 % 32768 + partial64 a b 1 0 % 32768
  | 2 => partial64 a b 0 1 / 32768 + partial64 a b 0 2 % 32768 + partial64 a b 1 0 / 32768 + partial64 a b 1 1 % 32768 + partial64 a b 2 0 % 32768
  | 3 => partial64 a b 0 2 / 32768 + partial64 a b 0 3 % 32768 + partial64 a b 1 1 / 32768 + partial64 a b 1 2 % 32768 + partial64 a b 2 0 / 32768 + partial64 a b 2 1 % 32768 + partial64 a b 3 0 % 32768
  | 4 => partial64 a b 0 3 / 32768 + partial64 a b 0 4 % 32768 + partial64 a b 1 2 / 32768 + partial64 a b 1 3 % 32768 + partial64 a b 2 1 / 32768 + partial64 a b 2 2 % 32768 + partial64 a b 3 0 / 32768 + partial64 a b 3 1 % 32768 + partial64 a b 4 0 % 32768
  | 5 => partial64 a b 0 4 / 32768 + partial64 a b 1 3 / 32768 + partial64 a b 1 4 % 32768 + partial64 a b 2 2 / 32768 + partial64 a b 2 3 % 32768 + partial64 a b 3 1 / 32768 + partial64 a b 3 2 % 32768 + partial64 a b 4 0 / 32768 + partial64 a b 4 1 % 32768
  | 6 => partial64 a b 1 4 / 32768 + partial64 a b 2 3 / 32768 + partial64 a b 2 4 % 32768 + partial64 a b 3 2 / 32768 + partial64 a b 3 3 % 32768 + partial64 a b 4 1 / 32768 + partial64 a b 4 2 % 32768
  | 7 => partial64 a b 2 4 / 32768 + partial64 a b 3 3 / 32768 + partial64 a b 3 4 % 32768 + partial64 a b 4 2 / 32768 + partial64 a b 4 3 % 32768
  | 8 => partial64 a b 3 4 / 32768 + partial64 a b 4 3 / 32768 + partial64 a b 4 4
  | _ => 0

def merged64 (a b : Nat) : Nat → Nat
  | 0 => coefficient64 a b 0
  | index + 1 => coefficient64 a b (index + 1) + merged64 a b index / 32768

theorem split15_64 (value : Nat) :
    value = 1 * (value / 1 % 32768) + 32768 * (value / 32768 % 32768) + 1073741824 * (value / 1073741824 % 32768) + 35184372088832 * (value / 35184372088832 % 32768) + 1152921504606846976 * (value / 1152921504606846976) := by
  have d0 := Nat.mod_add_div (value / 1) 32768
  have d1 := Nat.mod_add_div (value / 32768) 32768
  have d2 := Nat.mod_add_div (value / 1073741824) 32768
  have d3 := Nat.mod_add_div (value / 35184372088832) 32768
  norm_num only [Nat.div_one, Nat.div_div_eq_div_mul] at d0 d1 d2 d3
  omega

theorem product64_expansion (a b : Nat) :
    a * b = 1 * coefficient64 a b 0 + 32768 * coefficient64 a b 1 + 1073741824 * coefficient64 a b 2 + 35184372088832 * coefficient64 a b 3 + 1152921504606846976 * coefficient64 a b 4 + 37778931862957161709568 * coefficient64 a b 5 + 1237940039285380274899124224 * coefficient64 a b 6 + 40564819207303340847894502572032 * coefficient64 a b 7 + 1329227995784915872903807060280344576 * coefficient64 a b 8 := by
  have first := split15_64 a
  have second := split15_64 b
  have expansion : a * b =
      1 * partial64 a b 0 0 + 32768 * partial64 a b 0 1 + 1073741824 * partial64 a b 0 2 + 35184372088832 * partial64 a b 0 3 + 1152921504606846976 * partial64 a b 0 4 + 32768 * partial64 a b 1 0 + 1073741824 * partial64 a b 1 1 + 35184372088832 * partial64 a b 1 2 + 1152921504606846976 * partial64 a b 1 3 + 37778931862957161709568 * partial64 a b 1 4 + 1073741824 * partial64 a b 2 0 + 35184372088832 * partial64 a b 2 1 + 1152921504606846976 * partial64 a b 2 2 + 37778931862957161709568 * partial64 a b 2 3 + 1237940039285380274899124224 * partial64 a b 2 4 + 35184372088832 * partial64 a b 3 0 + 1152921504606846976 * partial64 a b 3 1 + 37778931862957161709568 * partial64 a b 3 2 + 1237940039285380274899124224 * partial64 a b 3 3 + 40564819207303340847894502572032 * partial64 a b 3 4 + 1152921504606846976 * partial64 a b 4 0 + 37778931862957161709568 * partial64 a b 4 1 + 1237940039285380274899124224 * partial64 a b 4 2 + 40564819207303340847894502572032 * partial64 a b 4 3 + 1329227995784915872903807060280344576 * partial64 a b 4 4 := by
    calc
      a * b = (1 * (a / 1 % 32768) + 32768 * (a / 32768 % 32768) + 1073741824 * (a / 1073741824 % 32768) + 35184372088832 * (a / 35184372088832 % 32768) + 1152921504606846976 * (a / 1152921504606846976)) *
        (1 * (b / 1 % 32768) + 32768 * (b / 32768 % 32768) + 1073741824 * (b / 1073741824 % 32768) + 35184372088832 * (b / 35184372088832 % 32768) + 1152921504606846976 * (b / 1152921504606846976)) :=
          congrArg₂ (· * ·) first second
      _ = _ := by norm_num [partial64, digit15]; ring
  rw [expansion]
  have p00 := Nat.mod_add_div (partial64 a b 0 0) 32768
  have p01 := Nat.mod_add_div (partial64 a b 0 1) 32768
  have p02 := Nat.mod_add_div (partial64 a b 0 2) 32768
  have p03 := Nat.mod_add_div (partial64 a b 0 3) 32768
  have p04 := Nat.mod_add_div (partial64 a b 0 4) 32768
  have p10 := Nat.mod_add_div (partial64 a b 1 0) 32768
  have p11 := Nat.mod_add_div (partial64 a b 1 1) 32768
  have p12 := Nat.mod_add_div (partial64 a b 1 2) 32768
  have p13 := Nat.mod_add_div (partial64 a b 1 3) 32768
  have p14 := Nat.mod_add_div (partial64 a b 1 4) 32768
  have p20 := Nat.mod_add_div (partial64 a b 2 0) 32768
  have p21 := Nat.mod_add_div (partial64 a b 2 1) 32768
  have p22 := Nat.mod_add_div (partial64 a b 2 2) 32768
  have p23 := Nat.mod_add_div (partial64 a b 2 3) 32768
  have p24 := Nat.mod_add_div (partial64 a b 2 4) 32768
  have p30 := Nat.mod_add_div (partial64 a b 3 0) 32768
  have p31 := Nat.mod_add_div (partial64 a b 3 1) 32768
  have p32 := Nat.mod_add_div (partial64 a b 3 2) 32768
  have p33 := Nat.mod_add_div (partial64 a b 3 3) 32768
  have p34 := Nat.mod_add_div (partial64 a b 3 4) 32768
  have p40 := Nat.mod_add_div (partial64 a b 4 0) 32768
  have p41 := Nat.mod_add_div (partial64 a b 4 1) 32768
  have p42 := Nat.mod_add_div (partial64 a b 4 2) 32768
  have p43 := Nat.mod_add_div (partial64 a b 4 3) 32768
  dsimp only [coefficient64]
  omega

theorem product64_no_overflow (a b : Nat) (bounded : a * b < 18446744073709551616) :
    coefficient64 a b 5 = 0 ∧ coefficient64 a b 6 = 0 ∧
    coefficient64 a b 7 = 0 ∧ coefficient64 a b 8 = 0 := by
  have expansion := product64_expansion a b
  omega

theorem product64_merge (a b : Nat) (bounded : a * b < 18446744073709551616) :
    merged64 a b 4 < 16 ∧
    a * b % 65536 = coefficient64 a b 0 + 32768 * (merged64 a b 1 % 32768 % 2) ∧
    a * b / 65536 % 65536 = merged64 a b 1 % 32768 / 2 +
      16384 * (merged64 a b 2 % 32768 % 4) ∧
    a * b / 4294967296 % 65536 = merged64 a b 2 % 32768 / 4 +
      8192 * (merged64 a b 3 % 32768 % 8) ∧
    a * b / 281474976710656 = merged64 a b 3 % 32768 / 8 + 4096 * merged64 a b 4 := by
  have expansion := product64_expansion a b
  obtain ⟨o5,o6,o7,o8⟩ := product64_no_overflow a b bounded
  rw [o5,o6,o7,o8] at expansion
  simp only [mul_zero,add_zero,one_mul] at expansion
  have c0 : coefficient64 a b 0 < 32768 := Nat.mod_lt _ (by decide)
  have m0 : merged64 a b 0 = coefficient64 a b 0 := rfl
  have m1 : merged64 a b 1 = coefficient64 a b 1 + merged64 a b 0 / 32768 := rfl
  have m2 : merged64 a b 2 = coefficient64 a b 2 + merged64 a b 1 / 32768 := rfl
  have m3 : merged64 a b 3 = coefficient64 a b 3 + merged64 a b 2 / 32768 := rfl
  have m4 : merged64 a b 4 = coefficient64 a b 4 + merged64 a b 3 / 32768 := rfl
  omega

theorem partial64_bound (a b i j : Nat) (aBound : a < 18446744073709551616)
    (bBound : b < 18446744073709551616) : partial64 a b i j < 1073741824 := by
  have aCap : (if i = 4 then a / 1152921504606846976 else digit15 a i) ≤ 32767 := by
    split_ifs
    · omega
    · have bound := Nat.mod_lt (a / 32768 ^ i) (by decide : 0 < 32768)
      exact Nat.le_pred_of_lt bound
  have bCap : (if j = 4 then b / 1152921504606846976 else digit15 b j) ≤ 32767 := by
    split_ifs
    · omega
    · have bound := Nat.mod_lt (b / 32768 ^ j) (by decide : 0 < 32768)
      exact Nat.le_pred_of_lt bound
  exact lt_of_le_of_lt (Nat.mul_le_mul aCap bCap) (by decide)

theorem product64_coefficient1_bound (a b : Nat) (aBound : a < 18446744073709551616)
    (bBound : b < 18446744073709551616) : coefficient64 a b 1 < 98304 := by
  have p00 := partial64_bound a b 0 0 aBound bBound
  dsimp only [coefficient64]
  omega

theorem product64_coefficient2_bound (a b : Nat) (aBound : a < 18446744073709551616)
    (bBound : b < 18446744073709551616) : coefficient64 a b 2 < 163840 := by
  have p01 := partial64_bound a b 0 1 aBound bBound
  have p10 := partial64_bound a b 1 0 aBound bBound
  dsimp only [coefficient64]
  omega

theorem product64_coefficient3_bound (a b : Nat) (aBound : a < 18446744073709551616)
    (bBound : b < 18446744073709551616) : coefficient64 a b 3 < 229376 := by
  have p02 := partial64_bound a b 0 2 aBound bBound
  have p11 := partial64_bound a b 1 1 aBound bBound
  have p20 := partial64_bound a b 2 0 aBound bBound
  dsimp only [coefficient64]
  omega

theorem product64_carry_bounds (a b : Nat) (aBound : a < 18446744073709551616)
    (bBound : b < 18446744073709551616) :
    merged64 a b 1 / 32768 < 4 ∧ merged64 a b 2 / 32768 < 8 ∧ merged64 a b 3 / 32768 < 8 := by
  have c0 : coefficient64 a b 0 < 32768 := Nat.mod_lt _ (by decide)
  have c1 := product64_coefficient1_bound a b aBound bBound
  have c2 := product64_coefficient2_bound a b aBound bBound
  have c3 := product64_coefficient3_bound a b aBound bBound
  have m0 : merged64 a b 0 = coefficient64 a b 0 := rfl
  have m1 : merged64 a b 1 = coefficient64 a b 1 + merged64 a b 0 / 32768 := rfl
  have m2 : merged64 a b 2 = coefficient64 a b 2 + merged64 a b 1 / 32768 := rfl
  have m3 : merged64 a b 3 = coefficient64 a b 3 + merged64 a b 2 / 32768 := rfl
  omega

theorem chunk64_bound (value index : Nat) (bounded : value < 18446744073709551616) :
    (if index = 4 then value / 1152921504606846976 else digit15 value index) ≤ 32767 := by
  split_ifs
  · omega
  · exact Nat.le_pred_of_lt (Nat.mod_lt _ (by decide))

theorem partial64_edge_bound (a b i j : Nat) (aBound : a < 18446744073709551616)
    (bBound : b < 18446744073709551616) (edge : i = 4 ∨ j = 4) :
    partial64 a b i j < 524288 := by
  rcases edge with rfl | rfl
  · have aCap : a / 1152921504606846976 ≤ 15 := by omega
    have bCap := chunk64_bound b j bBound
    exact lt_of_le_of_lt (Nat.mul_le_mul aCap bCap) (by decide)
  · have aCap := chunk64_bound a i aBound
    have bCap : b / 1152921504606846976 ≤ 15 := by omega
    exact lt_of_le_of_lt (Nat.mul_le_mul aCap bCap) (by decide)

theorem partial64_last_bound (a b : Nat) (aBound : a < 18446744073709551616)
    (bBound : b < 18446744073709551616) : partial64 a b 4 4 < 256 := by
  have aCap : a / 1152921504606846976 ≤ 15 := by omega
  have bCap : b / 1152921504606846976 ≤ 15 := by omega
  exact lt_of_le_of_lt (Nat.mul_le_mul aCap bCap) (by decide)

theorem split16_64 (value : Nat) :
    value = 281474976710656 * (value / 281474976710656) +
      4294967296 * (value / 4294967296 % 65536) +
      65536 * (value / 65536 % 65536) + value % 65536 := by
  have d0 := Nat.mod_add_div value 65536
  have d1 := Nat.mod_add_div (value / 65536) 65536
  have d2 := Nat.mod_add_div (value / 4294967296) 65536
  rw [Nat.div_div_eq_div_mul] at d1 d2
  norm_num only at d1 d2
  omega

end DivRemFV

