import DivRemFV.Air
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace DivRemFV

abbrev K := ZMod fieldModulus

def Expr.evalField (tables : Tables) (mid : Nat) (row : Int) : Expr → K
  | .constant value => value.val
  | .column col shift => (readCell tables mid col (row + shift)).val
  | .add a b => a.evalField tables mid row + b.evalField tables mid row
  | .sub a b => a.evalField tables mid row - b.evalField tables mid row
  | .mul a b => a.evalField tables mid row * b.evalField tables mid row

theorem Expr.eval_field_bridge (tables : Tables) (mid : Nat) (row : Int) (expr : Expr) :
    (expr.eval tables mid row : K) = expr.evalField tables mid row := by
  induction expr with
  | constant _ => rfl
  | column _ _ => rfl
  | add a b ha hb =>
    simp only [Expr.eval, Expr.evalField, ZMod.natCast_mod, Nat.cast_add, ha, hb]
  | mul a b ha hb =>
    simp only [Expr.eval, Expr.evalField, ZMod.natCast_mod, Nat.cast_mul, ha, hb]
  | sub a b ha hb =>
    have bound := b.eval_canonical tables mid row
    have enough : b.eval tables mid row ≤ a.eval tables mid row + fieldModulus := by omega
    simp only [Expr.eval, Expr.evalField, ZMod.natCast_mod, Nat.cast_sub enough,
      Nat.cast_add, ZMod.natCast_self, add_zero, ha, hb]

theorem lift_field_equality (a b : Nat) (ha : a < fieldModulus) (hb : b < fieldModulus)
    (equal : (a : K) = (b : K)) : a = b := by
  have values := congrArg ZMod.val equal
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using values

theorem lift_integer_zero (value : Int)
    (lower : -(fieldModulus : Int) < value) (upper : value < fieldModulus)
    (zero : (value : K) = 0) : value = 0 := by
  obtain ⟨multiple, identity⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd value fieldModulus).1 zero
  norm_num [fieldModulus] at lower upper identity
  omega

theorem lift_partial_product (a b low high : Nat)
    (ha : a < 32768) (hb : b < 32768) (hlow : low < 32768) (hhigh : high < 32768)
    (equation : (low : K) + 32768 * (high : K) = (a : K) * (b : K)) :
    low + 32768 * high = a * b := by
  apply lift_field_equality
  · dsimp [fieldModulus]
    omega
  · dsimp [fieldModulus]
    nlinarith [Nat.mul_le_mul (Nat.le_of_lt ha) (Nat.le_of_lt hb)]
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using equation

end DivRemFV
