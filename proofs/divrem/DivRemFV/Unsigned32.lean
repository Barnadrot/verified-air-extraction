import DivRemFV.Generated.Artifact
import DivRemFV.Arithmetic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.ClearExcept
import Mathlib.Tactic.Ring

set_option maxHeartbeats 300000
set_option Elab.async false

namespace DivRemFV
open Generated


def pairValue (v : Nat → Nat) (hi lo : Nat) : Nat := 65536 * v hi + v lo

private theorem minus_one_constant : (2130706432 : K) = -1 := by
  change ((fieldModulus - 1 : Nat) : K) = -1
  rw [Nat.cast_sub (by decide), ZMod.natCast_self, Nat.cast_one]
  exact zero_sub 1

open Lean Elab Tactic Meta in
elab "range_omega" : tactic => do
  let context ← getLCtx
  let mut remove := #[]
  for declaration in context do
    let name := declaration.userName.toString
    let keep := (name.startsWith "b" && (name.drop 1).toString.toNat?.isSome) || name == "productBound"
    if !keep then remove := remove.push declaration.fvarId
  liftMetaTactic1 fun goal => goal.tryClearMany remove
  evalTactic (← `(tactic| omega))

macro "lift_air" h:term : tactic =>
  `(tactic| (apply lift_field_equality
             · dsimp [fieldModulus]; range_omega
             · dsimp [fieldModulus]; range_omega
             · have equation := $h
               push_cast
               linear_combination equation))

theorem unsigned32_nonzero_arithmetic (v : Nat → Nat)
    (bounds : Bounds63 v) (h : Equations63 (fun i => (v i : K)))
    (active : v 51 = 1) (nonzero : v 17 = 1) :
    pairValue v 0 1 = pairValue v 2 3 * pairValue v 4 5 + pairValue v 6 7 ∧
    pairValue v 2 3 = pairValue v 6 7 + pairValue v 8 9 + 1 := by
  rcases bounds with ⟨b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,
    b16,b17,b18,b19,b20,b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32,b33,
    b34,b35,b36,b37,b38,b39,b40,b41,b42,b43,b44,b45,b46,b47,b48,b49,b50,b51⟩
  have zero : v 16 = 0 := by clear * - b16; omega
  have ret : (v 51 : K) = 1 := by simp [active]
  have flag : (v 17 : K) = 1 := by simp [nonzero]
  have czero : (v 16 : K) = 0 := by simp [zero]
  rcases h with ⟨h11992,h11993,h11994,h11995,h11996,h11997,h11998,h11999,h12000,h12001,h12002,h12003,h12004,h12005,h12006,h12007,h12008,h12009,h12010,h12011,h12012,h12013,h12014,h12015,h12016,h12017,h12018,h12019,h12020,h12021,h12022,h12023,h12024,h12041,h12042,h12044,h12049,h12070,h12074,h12075,h12076⟩
  simp only [ret, flag, czero, zero_add, one_mul, mul_one, minus_one_constant,
    neg_mul, sub_zero] at h11992 h11993 h11994 h11995 h11996 h11997 h11998 h11999 h12000 h12001 h12002 h12003 h12004 h12005 h12006 h12007 h12008 h12009 h12010 h12011 h12012 h12013 h12014 h12015 h12016 h12017 h12018 h12019 h12020 h12021 h12022 h12023 h12024 h12041 h12042 h12044 h12049 h12070 h12074 h12075 h12076
  have qlo : v 18 + 32768 * v 19 = v 5 := by lift_air h11997
  have qhi : v 20 + 16384 * v 21 = v 4 := by lift_air h11998
  have qmid : v 22 = v 19 + 2 * v 20 := by lift_air h11999
  have blo : v 23 + 32768 * v 24 = v 3 := by lift_air h12000
  have bhi : v 25 + 16384 * v 26 = v 2 := by lift_air h12001
  have bmid : v 27 = v 24 + 2 * v 25 := by lift_air h12002
  have p0 : v 28 + 32768 * v 29 = v 18 * v 23 :=
    lift_partial_product _ _ _ _ b18 b23 b28 b29 (sub_eq_zero.mp h12003)
  have p1 : v 30 + 32768 * v 31 = v 18 * v 27 :=
    lift_partial_product _ _ _ _ b18 b27 b30 b31 (sub_eq_zero.mp h12004)
  have p2 : v 32 + 32768 * v 33 = v 18 * v 26 :=
    lift_partial_product _ _ _ _ b18 (Nat.lt_trans b26 (by decide)) b32 (Nat.lt_trans b33 (by decide)) (sub_eq_zero.mp h12005)
  have p3 : v 34 + 32768 * v 35 = v 22 * v 23 :=
    lift_partial_product _ _ _ _ b22 b23 b34 b35 (sub_eq_zero.mp h12006)
  have p4 : v 36 + 32768 * v 37 = v 22 * v 27 :=
    lift_partial_product _ _ _ _ b22 b27 b36 b37 (sub_eq_zero.mp h12007)
  have p5 : v 38 + 32768 * v 39 = v 22 * v 26 :=
    lift_partial_product _ _ _ _ b22 (Nat.lt_trans b26 (by decide)) b38 (Nat.lt_trans b39 (by decide)) (sub_eq_zero.mp h12008)
  have p6 : v 40 + 32768 * v 41 = v 21 * v 23 :=
    lift_partial_product _ _ _ _ (Nat.lt_trans b21 (by decide)) b23 b40 (Nat.lt_trans b41 (by decide)) (sub_eq_zero.mp h12009)
  have p7 : v 42 + 32768 * v 43 = v 21 * v 27 :=
    lift_partial_product _ _ _ _ (Nat.lt_trans b21 (by decide)) b27 b42 (Nat.lt_trans b43 (by decide)) (sub_eq_zero.mp h12010)
  have p8 : v 44 = v 21 * v 26 := by
    apply lift_field_equality
    · dsimp [fieldModulus]; clear * - b44; omega
    · have productBound := Nat.mul_le_mul (Nat.le_of_lt b21) (Nat.le_of_lt b26)
      dsimp [fieldModulus]; clear * - productBound; omega
    · simpa only [Nat.cast_mul] using sub_eq_zero.mp h12011
  have merge0 : v 45 + 2 * v 46 + 32768 * v 47 = v 29 + v 30 + v 34 := by
    lift_air h12012
  have merge1 : v 48 = v 31 + v 32 + v 35 + v 36 + v 40 + v 47 := by
    lift_air h12013
  have overflow : v 33 + v 37 + v 38 + v 41 + v 42 + v 39 + v 43 + v 44 = 0 := by
    lift_air h12014
  have productLo : v 11 = v 28 + 32768 * v 45 := by lift_air h12015
  have productHi : v 10 = v 46 + 16384 * v 48 := by lift_air h12016
  have addLo : v 13 + 65536 * v 49 = v 11 + v 7 := by lift_air h12017
  have addHi : v 12 = v 10 + v 6 + v 49 := by lift_air h12018
  have dividendLo : v 1 = v 13 := by lift_air h12019
  have dividendHi : v 0 = v 12 := by lift_air h12020
  have boundLo : v 15 + 65536 * v 50 = v 7 + v 9 + 1 := by lift_air h12021
  have boundHi : v 14 = v 6 + v 8 + v 50 := by lift_air h12022
  have divisorLo : v 3 = v 15 := by lift_air h12023
  have divisorHi : v 2 = v 14 := by lift_air h12024
  have qsplit : pairValue v 4 5 = v 18 + 32768 * v 22 + 1073741824 * v 21 := by
    dsimp [pairValue]; clear * - qlo qhi qmid; omega
  have bsplit : pairValue v 2 3 = v 23 + 32768 * v 27 + 1073741824 * v 26 := by
    dsimp [pairValue]; clear * - blo bhi bmid; omega
  have product : pairValue v 4 5 * pairValue v 2 3 = pairValue v 10 11 := by
    rw [qsplit, bsplit]
    dsimp [pairValue]
    have zeros : v 33 = 0 ∧ v 37 = 0 ∧ v 38 = 0 ∧ v 41 = 0 ∧
        v 42 = 0 ∧ v 39 = 0 ∧ v 43 = 0 ∧ v 44 = 0 := by clear * - overflow; omega
    rcases zeros with ⟨z33,z37,z38,z41,z42,z39,z43,z44⟩
    simp only [z33,z37,z38,z41,z42,z39,z43,z44,mul_zero,add_zero] at p0 p1 p2 p3 p4 p5 p6 p7 p8
    have expanded :
        (v 18 + 32768 * v 22 + 1073741824 * v 21) *
          (v 23 + 32768 * v 27 + 1073741824 * v 26) =
        v 28 + 32768 * (v 29 + v 30 + v 34) +
          1073741824 * (v 31 + v 32 + v 35 + v 36 + v 40) := by
      calc
        _ = v 18 * v 23 + 32768 * (v 18 * v 27 + v 22 * v 23) +
          1073741824 * (v 18 * v 26 + v 22 * v 27 + v 21 * v 23) +
          35184372088832 * (v 22 * v 26 + v 21 * v 27) +
          1152921504606846976 * (v 21 * v 26) := by ring
        _ = _ := by rw [← p0, ← p1, ← p2, ← p3, ← p4, ← p5, ← p6, ← p7, ← p8]; ring
    clear * - expanded merge0 merge1 productLo productHi
    omega
  constructor
  · rw [Nat.mul_comm (pairValue v 2 3), product]
    dsimp [pairValue]; clear * - addLo addHi dividendLo dividendHi; omega
  · dsimp [pairValue]; clear * - boundLo boundHi divisorLo divisorHi; omega

theorem unsigned32_result (v : Nat → Nat)
    (bounds : Bounds63 v) (h : Equations63 (fun i => (v i : K)))
    (active : v 51 ≠ 0) :
    pairValue v 4 5 = (if pairValue v 2 3 = 0 then 4294967295 else pairValue v 0 1 / pairValue v 2 3) ∧
    pairValue v 6 7 = (if pairValue v 2 3 = 0 then pairValue v 0 1 else pairValue v 0 1 % pairValue v 2 3) := by
  have b0 := bounds.b0; have b1 := bounds.b1
  have b2 := bounds.b2; have b3 := bounds.b3
  have b4 := bounds.b4; have b5 := bounds.b5
  have b6 := bounds.b6; have b7 := bounds.b7
  have b17 := bounds.b17; have b51 := bounds.b51
  have activeOne : v 51 = 1 := by clear * - b51 active; omega
  have ret : (v 51 : K) = 1 := by simp [activeOne]
  have flags : v 17 = 0 ∨ v 17 = 1 := by clear * - b17; omega
  rcases flags with flagZero | flagOne
  · have flag : (v 17 : K) = 0 := by simp [flagZero]
    have check := h.h11994
    simp only [ret, flag, zero_add, one_mul, mul_one, sub_zero] at check
    have sum : v 2 + v 3 + 131070 = v 5 + v 4 := by lift_air check
    have divisorZero : pairValue v 2 3 = 0 := by dsimp [pairValue]; clear * - sum b4 b5; omega
    have q4 : v 4 = 65535 := by clear * - sum b4 b5; omega
    have q5 : v 5 = 65535 := by clear * - sum b4 b5; omega
    have loCheck := h.h11995
    have hiCheck := h.h11996
    simp only [ret, flag, one_mul, mul_one, sub_zero] at loCheck hiCheck
    have remainderLo : v 7 = v 1 := by lift_air loCheck
    have remainderHi : v 6 = v 0 := by lift_air hiCheck
    simp only [divisorZero, ↓reduceIte]
    constructor
    · simp [pairValue, q4, q5]
    · dsimp [pairValue]; clear * - remainderLo remainderHi; omega
  · have divisorPositive : 0 < pairValue v 2 3 := by
      by_contra notPositive
      have z2 : v 2 = 0 := by dsimp [pairValue] at notPositive; clear * - notPositive; omega
      have z3 : v 3 = 0 := by dsimp [pairValue] at notPositive; clear * - notPositive; omega
      have check := h.h11993
      norm_num [activeOne, flagOne, z2, z3] at check
    have arithmetic := unsigned32_nonzero_arithmetic v bounds h activeOne flagOne
    have result := (unsigned_hint_iff _ _ _ _ divisorPositive).1
      ⟨pairValue v 8 9, arithmetic⟩
    simpa only [Nat.ne_of_gt divisorPositive, ↓reduceIte] using result

theorem unsigned32_air_sound (tables : Tables) (row : Nat)
    (inside : row < (tables 63).size) (accepted : ConstraintsHold tables Generated.constraints)
    (ranges : StaticRanges tables) (active : readCell tables 63 51 row ≠ 0) :
    let v := fun col => (readCell tables 63 col row).val
    pairValue v 4 5 = (if pairValue v 2 3 = 0 then 4294967295 else pairValue v 0 1 / pairValue v 2 3) ∧
    pairValue v 6 7 = (if pairValue v 2 3 = 0 then pairValue v 0 1 else pairValue v 0 1 % pairValue v 2 3) := by
  apply unsigned32_result _ (bounds63 tables row inside accepted ranges)
    (equations63 tables row inside accepted)
  intro zero
  exact active (Fin.ext zero)

def encodeLimb (value : Nat) : Scalar :=
  ⟨value % 65536, Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)⟩

def encodePair (value : Nat) : Scalar × Scalar :=
  (encodeLimb (value / 65536), encodeLimb value)

theorem pair_limbs (high low : Scalar) (highBound : high.val < 65536)
    (lowBound : low.val < 65536) :
    (high, low) = encodePair (65536 * high.val + low.val) := by
  have result := (unsigned_divrem_iff (65536 * high.val + low.val) 65536 high.val low.val
    (by decide)).1 ⟨rfl, lowBound⟩
  apply Prod.ext
  · apply Fin.ext
    change high.val = ((65536 * high.val + low.val) / 65536) % 65536
    rw [← result.1, Nat.mod_eq_of_lt highBound]
  · apply Fin.ext
    exact result.2

theorem unsigned32_air_columns (tables : Tables) (row : Nat)
    (inside : row < (tables 63).size) (accepted : ConstraintsHold tables Generated.constraints)
    (fixed : StaticTablesFixed tables) (active : readCell tables 63 51 row ≠ 0) :
    let v := fun col => (readCell tables 63 col row).val
    let q := if pairValue v 2 3 = 0 then 4294967295 else pairValue v 0 1 / pairValue v 2 3
    let r := if pairValue v 2 3 = 0 then pairValue v 0 1 else pairValue v 0 1 % pairValue v 2 3
    (readCell tables 63 4 row, readCell tables 63 5 row) = encodePair q ∧
    (readCell tables 63 6 row, readCell tables 63 7 row) = encodePair r := by
  have ranges := fixed_tables_have_ranges tables fixed
  have bounds := bounds63 tables row inside accepted ranges
  have result := unsigned32_air_sound tables row inside accepted ranges active
  have q := pair_limbs (readCell tables 63 4 row) (readCell tables 63 5 row) bounds.b4 bounds.b5
  have r := pair_limbs (readCell tables 63 6 row) (readCell tables 63 7 row) bounds.b6 bounds.b7
  change (readCell tables 63 4 row, readCell tables 63 5 row) =
    encodePair (pairValue (fun col => (readCell tables 63 col row).val) 4 5) at q
  change (readCell tables 63 6 row, readCell tables 63 7 row) =
    encodePair (pairValue (fun col => (readCell tables 63 col row).val) 6 7) at r
  rw [result.1] at q
  rw [result.2] at r
  exact ⟨q, r⟩

end DivRemFV




