import DivRemFV.Extension.Artifact
import DivRemFV.Intervals
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DivRemFV.Extension

def intervals67 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩
]
def columns67 (col : Nat) : Interval := intervals67[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds67 (tables : Tables) (row : Nat)
    (inside : row < (tables 67).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns67 col).Contains ((readCell tables 67 col row).val : Int) := by
  intro col
  have bound := (readCell tables 67 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 67 col row).val := by omega
  by_cases small : col < 10
  · have bounds := bounds67 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 67 0 row).val ∧
        ((readCell tables 67 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 67 1 row).val ∧
        ((readCell tables 67 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 67 2 row).val ∧
        ((readCell tables 67 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 67 3 row).val ∧
        ((readCell tables 67 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 67 4 row).val ∧
        ((readCell tables 67 4 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 67 5 row).val ∧
        ((readCell tables 67 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 67 6 row).val ∧
        ((readCell tables 67 6 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 67 7 row).val ∧
        ((readCell tables 67 7 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 67 8 row).val ∧
        ((readCell tables 67 8 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 67 9 row).val ∧
        ((readCell tables 67 9 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b9; omega
  · have missing : intervals67[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals67] using Nat.le_of_not_gt small
    simp only [columns67, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations67 (v : Nat → Int) : Prop where
  h12204 : (((1 : Int) * (v 9)) * ((v 8) - (v 1))) = 0
  h12205 : (((1 : Int) * (v 9)) * ((((0 : Int) + (v 7)) + (((1 : Int) * (32768 : Int)) * (v 6))) - (v 0))) = 0
  h12206 : ((((1 : Int) * (v 9)) * ((v 5) - (v 1))) * (v 6)) = 0
  h12207 : ((((1 : Int) * (v 9)) * ((v 4) - (v 0))) * (v 6)) = 0
  h12208 : (((1 : Int) * (v 9)) * (((0 : Int) + (((1 : Int) * ((65535 : Int) - (v 3))) * (v 6))) + (((1 : Int) * ((65535 : Int) - (v 2))) * (v 6)))) = 0
  h12209 : ((((1 : Int) * (v 9)) * ((1 : Int) - (v 6))) * ((v 5) - (v 1))) = 0
  h12210 : ((((1 : Int) * (v 9)) * ((1 : Int) - (v 6))) * ((v 4) - (v 0))) = 0
  h12211 : (((1 : Int) * (v 9)) * (((0 : Int) + (((1 : Int) * ((1 : Int) - (v 6))) * (v 3))) + (((1 : Int) * ((1 : Int) - (v 6))) * (v 2)))) = 0
  h12218 : ((((1 : Int) * (v 6)) * (v 6)) - (v 6)) = 0
  h12221 : ((((1 : Int) * (v 9)) * (v 9)) - (v 9)) = 0

theorem integer_equations67 (tables : Tables) (row : Nat)
    (inside : row < (tables 67).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations67 (fun col => ((readCell tables 67 col row).val : Int)) := by
  have bounded := column_bounds67 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c12204 member12204
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12204 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12204, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12205 member12205
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12205 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12205, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12206 member12206
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12206 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12206, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12207 member12207
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12207 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12207, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12208 member12208
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12208 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12208, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12209 member12209
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12209 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12209, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12210 member12210
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12210 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12210, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12211 member12211
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12211 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12211, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12218 member12218
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12218 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12218, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12221 member12221
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12221 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 67 row columns67 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12221, Expr.evalInteger, integerConstant, fieldModulus] using lifted

end DivRemFV.Extension
