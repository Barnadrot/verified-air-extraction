import DivRemFV.Generated.Artifact
import DivRemFV.Intervals
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DivRemFV.Generated

def intervals55 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩
]
def columns55 (col : Nat) : Interval := intervals55[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds55 (tables : Tables) (row : Nat)
    (inside : row < (tables 55).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns55 col).Contains ((readCell tables 55 col row).val : Int) := by
  intro col
  have bound := (readCell tables 55 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 55 col row).val := by omega
  by_cases small : col < 28
  · have bounds := bounds55 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 55 0 row).val ∧
        ((readCell tables 55 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 55 1 row).val ∧
        ((readCell tables 55 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 55 2 row).val ∧
        ((readCell tables 55 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 55 3 row).val ∧
        ((readCell tables 55 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 55 4 row).val ∧
        ((readCell tables 55 4 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 55 5 row).val ∧
        ((readCell tables 55 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 55 6 row).val ∧
        ((readCell tables 55 6 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 55 7 row).val ∧
        ((readCell tables 55 7 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 55 8 row).val ∧
        ((readCell tables 55 8 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 55 9 row).val ∧
        ((readCell tables 55 9 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b9; omega
    · change (0 : Int) ≤ (readCell tables 55 10 row).val ∧
        ((readCell tables 55 10 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b10; omega
    · change (0 : Int) ≤ (readCell tables 55 11 row).val ∧
        ((readCell tables 55 11 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b11; omega
    · change (0 : Int) ≤ (readCell tables 55 12 row).val ∧
        ((readCell tables 55 12 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b12; omega
    · change (0 : Int) ≤ (readCell tables 55 13 row).val ∧
        ((readCell tables 55 13 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b13; omega
    · change (0 : Int) ≤ (readCell tables 55 14 row).val ∧
        ((readCell tables 55 14 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b14; omega
    · change (0 : Int) ≤ (readCell tables 55 15 row).val ∧
        ((readCell tables 55 15 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b15; omega
    · change (0 : Int) ≤ (readCell tables 55 16 row).val ∧
        ((readCell tables 55 16 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b16; omega
    · change (0 : Int) ≤ (readCell tables 55 17 row).val ∧
        ((readCell tables 55 17 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b17; omega
    · change (0 : Int) ≤ (readCell tables 55 18 row).val ∧
        ((readCell tables 55 18 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b18; omega
    · change (0 : Int) ≤ (readCell tables 55 19 row).val ∧
        ((readCell tables 55 19 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b19; omega
    · change (0 : Int) ≤ (readCell tables 55 20 row).val ∧
        ((readCell tables 55 20 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b20; omega
    · change (0 : Int) ≤ (readCell tables 55 21 row).val ∧
        ((readCell tables 55 21 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b21; omega
    · change (0 : Int) ≤ (readCell tables 55 22 row).val ∧
        ((readCell tables 55 22 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b22; omega
    · change (0 : Int) ≤ (readCell tables 55 23 row).val ∧
        ((readCell tables 55 23 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b23; omega
    · change (0 : Int) ≤ (readCell tables 55 24 row).val ∧
        ((readCell tables 55 24 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b24; omega
    · change (0 : Int) ≤ (readCell tables 55 25 row).val ∧
        ((readCell tables 55 25 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b25; omega
    · change (0 : Int) ≤ (readCell tables 55 26 row).val ∧
        ((readCell tables 55 26 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b26; omega
    · change (0 : Int) ≤ (readCell tables 55 27 row).val ∧
        ((readCell tables 55 27 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b27; omega
  · have missing : intervals55[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals55] using Nat.le_of_not_gt small
    simp only [columns55, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations55 (v : Nat → Int) : Prop where
  h11150 : (((1 : Int) * (v 27)) * ((v 20) - (v 3))) = 0
  h11151 : (((1 : Int) * (v 27)) * ((v 19) - (v 2))) = 0
  h11152 : (((1 : Int) * (v 27)) * ((v 18) - (v 1))) = 0
  h11153 : (((1 : Int) * (v 27)) * ((((0 : Int) + (v 17)) + (((1 : Int) * (32768 : Int)) * (v 8))) - (v 0))) = 0
  h11154 : ((((1 : Int) * (v 27)) * ((v 7) - (v 3))) * ((1 : Int) - (v 8))) = 0
  h11155 : ((((1 : Int) * (v 27)) * ((v 6) - (v 2))) * ((1 : Int) - (v 8))) = 0
  h11156 : ((((1 : Int) * (v 27)) * ((v 5) - (v 1))) * ((1 : Int) - (v 8))) = 0
  h11157 : ((((1 : Int) * (v 27)) * ((v 4) - (v 0))) * ((1 : Int) - (v 8))) = 0
  h11158 : (((1 : Int) * (v 27)) * (((((0 : Int) + (((1 : Int) * (v 8)) * ((65535 : Int) - (v 16)))) + (((1 : Int) * (v 8)) * ((65535 : Int) - (v 15)))) + (((1 : Int) * (v 8)) * ((65535 : Int) - (v 14)))) + (((1 : Int) * (v 8)) * ((65535 : Int) - (v 13))))) = 0
  h11159 : ((((1 : Int) * (v 27)) * (v 8)) * ((((v 12) - (v 16)) - (((1 : Int) * (-1 : Int)) * (v 3))) - (((1 : Int) * (65536 : Int)) * (v 21)))) = 0
  h11160 : ((((1 : Int) * (v 27)) * (v 8)) * (((((v 11) - (v 15)) - (((1 : Int) * (-1 : Int)) * (v 2))) - (((1 : Int) * (-1 : Int)) * (v 21))) - (((1 : Int) * (65536 : Int)) * (v 22)))) = 0
  h11161 : ((((1 : Int) * (v 27)) * (v 8)) * (((((v 10) - (v 14)) - (((1 : Int) * (-1 : Int)) * (v 1))) - (((1 : Int) * (-1 : Int)) * (v 22))) - (((1 : Int) * (65536 : Int)) * (v 23)))) = 0
  h11162 : ((((1 : Int) * (v 27)) * (v 8)) * ((((v 9) - (v 13)) - (((1 : Int) * (-1 : Int)) * (v 0))) - (((1 : Int) * (-1 : Int)) * (v 23)))) = 0
  h11163 : ((((1 : Int) * (v 27)) * (v 8)) * (((((0 : Int) + (v 7)) + (((1 : Int) * (65536 : Int)) * (v 24))) - (v 12)) - (1 : Int))) = 0
  h11164 : ((((1 : Int) * (v 27)) * (v 8)) * (((((0 : Int) + (v 6)) + (((1 : Int) * (65536 : Int)) * (v 25))) - (v 11)) - (v 24))) = 0
  h11165 : ((((1 : Int) * (v 27)) * (v 8)) * (((((0 : Int) + (v 5)) + (((1 : Int) * (65536 : Int)) * (v 26))) - (v 10)) - (v 25))) = 0
  h11166 : ((((1 : Int) * (v 27)) * (v 8)) * (((v 4) - (v 9)) - (v 26))) = 0
  h11175 : ((((1 : Int) * (v 8)) * (v 8)) - (v 8)) = 0
  h11188 : ((((1 : Int) * (v 21)) * (v 21)) - (v 21)) = 0
  h11189 : ((((1 : Int) * (v 22)) * (v 22)) - (v 22)) = 0
  h11190 : ((((1 : Int) * (v 23)) * (v 23)) - (v 23)) = 0
  h11191 : ((((1 : Int) * (v 24)) * (v 24)) - (v 24)) = 0
  h11192 : ((((1 : Int) * (v 25)) * (v 25)) - (v 25)) = 0
  h11193 : ((((1 : Int) * (v 26)) * (v 26)) - (v 26)) = 0
  h11194 : ((((1 : Int) * (v 27)) * (v 27)) - (v 27)) = 0

theorem integer_equations55 (tables : Tables) (row : Nat)
    (inside : row < (tables 55).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations55 (fun col => ((readCell tables 55 col row).val : Int)) := by
  have bounded := column_bounds55 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c11150 member11150
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11150 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11150, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11151 member11151
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11151 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11151, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11152 member11152
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11152 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11152, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11153 member11153
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11153 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11153, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11154 member11154
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11154 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11154, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11155 member11155
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11155 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11155, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11156 member11156
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11156 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11156, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11157 member11157
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11157 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11157, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11158 member11158
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11158 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11158, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11159 member11159
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11159 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11159, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11160 member11160
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11160 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11160, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11161 member11161
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11161 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11161, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11162 member11162
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11162 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11162, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11163 member11163
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11163 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11163, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11164 member11164
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11164 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11164, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11165 member11165
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11165 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11165, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11166 member11166
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11166 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11166, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11175 member11175
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11175 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11175, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11188 member11188
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11188 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11188, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11189 member11189
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11189 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11189, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11190 member11190
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11190 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11190, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11191 member11191
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11191 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11191, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11192 member11192
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11192 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11192, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11193 member11193
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11193 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11193, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11194 member11194
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11194 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 55 row columns55 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11194, Expr.evalInteger, integerConstant, fieldModulus] using lifted

def intervals56 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩
]
def columns56 (col : Nat) : Interval := intervals56[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds56 (tables : Tables) (row : Nat)
    (inside : row < (tables 56).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns56 col).Contains ((readCell tables 56 col row).val : Int) := by
  intro col
  have bound := (readCell tables 56 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 56 col row).val := by omega
  by_cases small : col < 14
  · have bounds := bounds56 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 56 0 row).val ∧
        ((readCell tables 56 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 56 1 row).val ∧
        ((readCell tables 56 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 56 2 row).val ∧
        ((readCell tables 56 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 56 3 row).val ∧
        ((readCell tables 56 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 56 4 row).val ∧
        ((readCell tables 56 4 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 56 5 row).val ∧
        ((readCell tables 56 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 56 6 row).val ∧
        ((readCell tables 56 6 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 56 7 row).val ∧
        ((readCell tables 56 7 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 56 8 row).val ∧
        ((readCell tables 56 8 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 56 9 row).val ∧
        ((readCell tables 56 9 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b9; omega
    · change (0 : Int) ≤ (readCell tables 56 10 row).val ∧
        ((readCell tables 56 10 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b10; omega
    · change (0 : Int) ≤ (readCell tables 56 11 row).val ∧
        ((readCell tables 56 11 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b11; omega
    · change (0 : Int) ≤ (readCell tables 56 12 row).val ∧
        ((readCell tables 56 12 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b12; omega
    · change (0 : Int) ≤ (readCell tables 56 13 row).val ∧
        ((readCell tables 56 13 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b13; omega
  · have missing : intervals56[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals56] using Nat.le_of_not_gt small
    simp only [columns56, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations56 (v : Nat → Int) : Prop where
  h11195 : (((1 : Int) * (v 13)) * ((v 10) - (v 1))) = 0
  h11196 : (((1 : Int) * (v 13)) * ((((0 : Int) + (v 9)) + (((1 : Int) * (32768 : Int)) * (v 4))) - (v 0))) = 0
  h11197 : ((((1 : Int) * (v 13)) * ((v 3) - (v 1))) * ((1 : Int) - (v 4))) = 0
  h11198 : ((((1 : Int) * (v 13)) * ((v 2) - (v 0))) * ((1 : Int) - (v 4))) = 0
  h11199 : (((1 : Int) * (v 13)) * (((0 : Int) + (((1 : Int) * (v 4)) * ((65535 : Int) - (v 8)))) + (((1 : Int) * (v 4)) * ((65535 : Int) - (v 7))))) = 0
  h11200 : ((((1 : Int) * (v 13)) * (v 4)) * ((((v 6) - (v 8)) - (((1 : Int) * (-1 : Int)) * (v 1))) - (((1 : Int) * (65536 : Int)) * (v 11)))) = 0
  h11201 : ((((1 : Int) * (v 13)) * (v 4)) * ((((v 5) - (v 7)) - (((1 : Int) * (-1 : Int)) * (v 0))) - (((1 : Int) * (-1 : Int)) * (v 11)))) = 0
  h11202 : ((((1 : Int) * (v 13)) * (v 4)) * (((((0 : Int) + (v 3)) + (((1 : Int) * (65536 : Int)) * (v 12))) - (v 6)) - (1 : Int))) = 0
  h11203 : ((((1 : Int) * (v 13)) * (v 4)) * (((v 2) - (v 5)) - (v 12))) = 0
  h11208 : ((((1 : Int) * (v 4)) * (v 4)) - (v 4)) = 0
  h11215 : ((((1 : Int) * (v 11)) * (v 11)) - (v 11)) = 0
  h11216 : ((((1 : Int) * (v 12)) * (v 12)) - (v 12)) = 0
  h11217 : ((((1 : Int) * (v 13)) * (v 13)) - (v 13)) = 0

theorem integer_equations56 (tables : Tables) (row : Nat)
    (inside : row < (tables 56).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations56 (fun col => ((readCell tables 56 col row).val : Int)) := by
  have bounded := column_bounds56 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c11195 member11195
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11195 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11195, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11196 member11196
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11196 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11196, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11197 member11197
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11197 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11197, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11198 member11198
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11198 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11198, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11199 member11199
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11199 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11199, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11200 member11200
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11200 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11200, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11201 member11201
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11201 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11201, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11202 member11202
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11202 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11202, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11203 member11203
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11203 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11203, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11208 member11208
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11208 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11208, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11215 member11215
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11215 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11215, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11216 member11216
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11216 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11216, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11217 member11217
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11217 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 56 row columns56 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11217, Expr.evalInteger, integerConstant, fieldModulus] using lifted

def intervals61 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 0⟩,
  ⟨0, 1⟩,
  ⟨0, 32767⟩,
  ⟨0, 1⟩,
  ⟨0, 16383⟩,
  ⟨0, 3⟩,
  ⟨0, 8191⟩,
  ⟨0, 7⟩,
  ⟨0, 4095⟩,
  ⟨0, 15⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 1⟩,
  ⟨0, 16383⟩,
  ⟨0, 3⟩,
  ⟨0, 8191⟩,
  ⟨0, 7⟩,
  ⟨0, 4095⟩,
  ⟨0, 15⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 15⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 15⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 15⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 15⟩,
  ⟨0, 32767⟩,
  ⟨0, 15⟩,
  ⟨0, 32767⟩,
  ⟨0, 15⟩,
  ⟨0, 32767⟩,
  ⟨0, 15⟩,
  ⟨0, 32767⟩,
  ⟨0, 15⟩,
  ⟨0, 255⟩,
  ⟨0, 1⟩,
  ⟨0, 16383⟩,
  ⟨0, 3⟩,
  ⟨0, 3⟩,
  ⟨0, 8191⟩,
  ⟨0, 7⟩,
  ⟨0, 7⟩,
  ⟨0, 4095⟩,
  ⟨0, 7⟩,
  ⟨0, 15⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 2130706432⟩
]
def columns61 (col : Nat) : Interval := intervals61[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds61 (tables : Tables) (row : Nat)
    (inside : row < (tables 61).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns61 col).Contains ((readCell tables 61 col row).val : Int) := by
  intro col
  have bound := (readCell tables 61 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 61 col row).val := by omega
  by_cases small : col < 123
  · have bounds := bounds61 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 61 0 row).val ∧
        ((readCell tables 61 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 61 1 row).val ∧
        ((readCell tables 61 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 61 2 row).val ∧
        ((readCell tables 61 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 61 3 row).val ∧
        ((readCell tables 61 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 61 4 row).val ∧
        ((readCell tables 61 4 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 61 5 row).val ∧
        ((readCell tables 61 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 61 6 row).val ∧
        ((readCell tables 61 6 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 61 7 row).val ∧
        ((readCell tables 61 7 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 61 8 row).val ∧
        ((readCell tables 61 8 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 61 9 row).val ∧
        ((readCell tables 61 9 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b9; omega
    · change (0 : Int) ≤ (readCell tables 61 10 row).val ∧
        ((readCell tables 61 10 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b10; omega
    · change (0 : Int) ≤ (readCell tables 61 11 row).val ∧
        ((readCell tables 61 11 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b11; omega
    · change (0 : Int) ≤ (readCell tables 61 12 row).val ∧
        ((readCell tables 61 12 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b12; omega
    · change (0 : Int) ≤ (readCell tables 61 13 row).val ∧
        ((readCell tables 61 13 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b13; omega
    · change (0 : Int) ≤ (readCell tables 61 14 row).val ∧
        ((readCell tables 61 14 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b14; omega
    · change (0 : Int) ≤ (readCell tables 61 15 row).val ∧
        ((readCell tables 61 15 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b15; omega
    · change (0 : Int) ≤ (readCell tables 61 16 row).val ∧
        ((readCell tables 61 16 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b16; omega
    · change (0 : Int) ≤ (readCell tables 61 17 row).val ∧
        ((readCell tables 61 17 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b17; omega
    · change (0 : Int) ≤ (readCell tables 61 18 row).val ∧
        ((readCell tables 61 18 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b18; omega
    · change (0 : Int) ≤ (readCell tables 61 19 row).val ∧
        ((readCell tables 61 19 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b19; omega
    · change (0 : Int) ≤ (readCell tables 61 20 row).val ∧
        ((readCell tables 61 20 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b20; omega
    · change (0 : Int) ≤ (readCell tables 61 21 row).val ∧
        ((readCell tables 61 21 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b21; omega
    · change (0 : Int) ≤ (readCell tables 61 22 row).val ∧
        ((readCell tables 61 22 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b22; omega
    · change (0 : Int) ≤ (readCell tables 61 23 row).val ∧
        ((readCell tables 61 23 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b23; omega
    · change (0 : Int) ≤ (readCell tables 61 24 row).val ∧
        ((readCell tables 61 24 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b24; omega
    · change (0 : Int) ≤ (readCell tables 61 25 row).val ∧
        ((readCell tables 61 25 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b25; omega
    · change (0 : Int) ≤ (readCell tables 61 26 row).val ∧
        ((readCell tables 61 26 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b26; omega
    · change (0 : Int) ≤ (readCell tables 61 27 row).val ∧
        ((readCell tables 61 27 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b27; omega
    · change (0 : Int) ≤ (readCell tables 61 28 row).val ∧
        ((readCell tables 61 28 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b28; omega
    · change (0 : Int) ≤ (readCell tables 61 29 row).val ∧
        ((readCell tables 61 29 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b29; omega
    · change (0 : Int) ≤ (readCell tables 61 30 row).val ∧
        ((readCell tables 61 30 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b30; omega
    · change (0 : Int) ≤ (readCell tables 61 31 row).val ∧
        ((readCell tables 61 31 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b31; omega
    · change (0 : Int) ≤ (readCell tables 61 32 row).val ∧
        ((readCell tables 61 32 row).val : Int) ≤ 0
      constructor
      · omega
      · have width := bounds.b32; omega
    · change (0 : Int) ≤ (readCell tables 61 33 row).val ∧
        ((readCell tables 61 33 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b33; omega
    · change (0 : Int) ≤ (readCell tables 61 34 row).val ∧
        ((readCell tables 61 34 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b34; omega
    · change (0 : Int) ≤ (readCell tables 61 35 row).val ∧
        ((readCell tables 61 35 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b35; omega
    · change (0 : Int) ≤ (readCell tables 61 36 row).val ∧
        ((readCell tables 61 36 row).val : Int) ≤ 16383
      constructor
      · omega
      · have width := bounds.b36; omega
    · change (0 : Int) ≤ (readCell tables 61 37 row).val ∧
        ((readCell tables 61 37 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b37; omega
    · change (0 : Int) ≤ (readCell tables 61 38 row).val ∧
        ((readCell tables 61 38 row).val : Int) ≤ 8191
      constructor
      · omega
      · have width := bounds.b38; omega
    · change (0 : Int) ≤ (readCell tables 61 39 row).val ∧
        ((readCell tables 61 39 row).val : Int) ≤ 7
      constructor
      · omega
      · have width := bounds.b39; omega
    · change (0 : Int) ≤ (readCell tables 61 40 row).val ∧
        ((readCell tables 61 40 row).val : Int) ≤ 4095
      constructor
      · omega
      · have width := bounds.b40; omega
    · change (0 : Int) ≤ (readCell tables 61 41 row).val ∧
        ((readCell tables 61 41 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b41; omega
    · change (0 : Int) ≤ (readCell tables 61 42 row).val ∧
        ((readCell tables 61 42 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b42; omega
    · change (0 : Int) ≤ (readCell tables 61 43 row).val ∧
        ((readCell tables 61 43 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b43; omega
    · change (0 : Int) ≤ (readCell tables 61 44 row).val ∧
        ((readCell tables 61 44 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b44; omega
    · change (0 : Int) ≤ (readCell tables 61 45 row).val ∧
        ((readCell tables 61 45 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b45; omega
    · change (0 : Int) ≤ (readCell tables 61 46 row).val ∧
        ((readCell tables 61 46 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b46; omega
    · change (0 : Int) ≤ (readCell tables 61 47 row).val ∧
        ((readCell tables 61 47 row).val : Int) ≤ 16383
      constructor
      · omega
      · have width := bounds.b47; omega
    · change (0 : Int) ≤ (readCell tables 61 48 row).val ∧
        ((readCell tables 61 48 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b48; omega
    · change (0 : Int) ≤ (readCell tables 61 49 row).val ∧
        ((readCell tables 61 49 row).val : Int) ≤ 8191
      constructor
      · omega
      · have width := bounds.b49; omega
    · change (0 : Int) ≤ (readCell tables 61 50 row).val ∧
        ((readCell tables 61 50 row).val : Int) ≤ 7
      constructor
      · omega
      · have width := bounds.b50; omega
    · change (0 : Int) ≤ (readCell tables 61 51 row).val ∧
        ((readCell tables 61 51 row).val : Int) ≤ 4095
      constructor
      · omega
      · have width := bounds.b51; omega
    · change (0 : Int) ≤ (readCell tables 61 52 row).val ∧
        ((readCell tables 61 52 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b52; omega
    · change (0 : Int) ≤ (readCell tables 61 53 row).val ∧
        ((readCell tables 61 53 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b53; omega
    · change (0 : Int) ≤ (readCell tables 61 54 row).val ∧
        ((readCell tables 61 54 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b54; omega
    · change (0 : Int) ≤ (readCell tables 61 55 row).val ∧
        ((readCell tables 61 55 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b55; omega
    · change (0 : Int) ≤ (readCell tables 61 56 row).val ∧
        ((readCell tables 61 56 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b56; omega
    · change (0 : Int) ≤ (readCell tables 61 57 row).val ∧
        ((readCell tables 61 57 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b57; omega
    · change (0 : Int) ≤ (readCell tables 61 58 row).val ∧
        ((readCell tables 61 58 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b58; omega
    · change (0 : Int) ≤ (readCell tables 61 59 row).val ∧
        ((readCell tables 61 59 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b59; omega
    · change (0 : Int) ≤ (readCell tables 61 60 row).val ∧
        ((readCell tables 61 60 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b60; omega
    · change (0 : Int) ≤ (readCell tables 61 61 row).val ∧
        ((readCell tables 61 61 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b61; omega
    · change (0 : Int) ≤ (readCell tables 61 62 row).val ∧
        ((readCell tables 61 62 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b62; omega
    · change (0 : Int) ≤ (readCell tables 61 63 row).val ∧
        ((readCell tables 61 63 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b63; omega
    · change (0 : Int) ≤ (readCell tables 61 64 row).val ∧
        ((readCell tables 61 64 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b64; omega
    · change (0 : Int) ≤ (readCell tables 61 65 row).val ∧
        ((readCell tables 61 65 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b65; omega
    · change (0 : Int) ≤ (readCell tables 61 66 row).val ∧
        ((readCell tables 61 66 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b66; omega
    · change (0 : Int) ≤ (readCell tables 61 67 row).val ∧
        ((readCell tables 61 67 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b67; omega
    · change (0 : Int) ≤ (readCell tables 61 68 row).val ∧
        ((readCell tables 61 68 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b68; omega
    · change (0 : Int) ≤ (readCell tables 61 69 row).val ∧
        ((readCell tables 61 69 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b69; omega
    · change (0 : Int) ≤ (readCell tables 61 70 row).val ∧
        ((readCell tables 61 70 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b70; omega
    · change (0 : Int) ≤ (readCell tables 61 71 row).val ∧
        ((readCell tables 61 71 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b71; omega
    · change (0 : Int) ≤ (readCell tables 61 72 row).val ∧
        ((readCell tables 61 72 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b72; omega
    · change (0 : Int) ≤ (readCell tables 61 73 row).val ∧
        ((readCell tables 61 73 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b73; omega
    · change (0 : Int) ≤ (readCell tables 61 74 row).val ∧
        ((readCell tables 61 74 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b74; omega
    · change (0 : Int) ≤ (readCell tables 61 75 row).val ∧
        ((readCell tables 61 75 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b75; omega
    · change (0 : Int) ≤ (readCell tables 61 76 row).val ∧
        ((readCell tables 61 76 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b76; omega
    · change (0 : Int) ≤ (readCell tables 61 77 row).val ∧
        ((readCell tables 61 77 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b77; omega
    · change (0 : Int) ≤ (readCell tables 61 78 row).val ∧
        ((readCell tables 61 78 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b78; omega
    · change (0 : Int) ≤ (readCell tables 61 79 row).val ∧
        ((readCell tables 61 79 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b79; omega
    · change (0 : Int) ≤ (readCell tables 61 80 row).val ∧
        ((readCell tables 61 80 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b80; omega
    · change (0 : Int) ≤ (readCell tables 61 81 row).val ∧
        ((readCell tables 61 81 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b81; omega
    · change (0 : Int) ≤ (readCell tables 61 82 row).val ∧
        ((readCell tables 61 82 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b82; omega
    · change (0 : Int) ≤ (readCell tables 61 83 row).val ∧
        ((readCell tables 61 83 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b83; omega
    · change (0 : Int) ≤ (readCell tables 61 84 row).val ∧
        ((readCell tables 61 84 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b84; omega
    · change (0 : Int) ≤ (readCell tables 61 85 row).val ∧
        ((readCell tables 61 85 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b85; omega
    · change (0 : Int) ≤ (readCell tables 61 86 row).val ∧
        ((readCell tables 61 86 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b86; omega
    · change (0 : Int) ≤ (readCell tables 61 87 row).val ∧
        ((readCell tables 61 87 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b87; omega
    · change (0 : Int) ≤ (readCell tables 61 88 row).val ∧
        ((readCell tables 61 88 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b88; omega
    · change (0 : Int) ≤ (readCell tables 61 89 row).val ∧
        ((readCell tables 61 89 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b89; omega
    · change (0 : Int) ≤ (readCell tables 61 90 row).val ∧
        ((readCell tables 61 90 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b90; omega
    · change (0 : Int) ≤ (readCell tables 61 91 row).val ∧
        ((readCell tables 61 91 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b91; omega
    · change (0 : Int) ≤ (readCell tables 61 92 row).val ∧
        ((readCell tables 61 92 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b92; omega
    · change (0 : Int) ≤ (readCell tables 61 93 row).val ∧
        ((readCell tables 61 93 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b93; omega
    · change (0 : Int) ≤ (readCell tables 61 94 row).val ∧
        ((readCell tables 61 94 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b94; omega
    · change (0 : Int) ≤ (readCell tables 61 95 row).val ∧
        ((readCell tables 61 95 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b95; omega
    · change (0 : Int) ≤ (readCell tables 61 96 row).val ∧
        ((readCell tables 61 96 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b96; omega
    · change (0 : Int) ≤ (readCell tables 61 97 row).val ∧
        ((readCell tables 61 97 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b97; omega
    · change (0 : Int) ≤ (readCell tables 61 98 row).val ∧
        ((readCell tables 61 98 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b98; omega
    · change (0 : Int) ≤ (readCell tables 61 99 row).val ∧
        ((readCell tables 61 99 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b99; omega
    · change (0 : Int) ≤ (readCell tables 61 100 row).val ∧
        ((readCell tables 61 100 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b100; omega
    · change (0 : Int) ≤ (readCell tables 61 101 row).val ∧
        ((readCell tables 61 101 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b101; omega
    · change (0 : Int) ≤ (readCell tables 61 102 row).val ∧
        ((readCell tables 61 102 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b102; omega
    · change (0 : Int) ≤ (readCell tables 61 103 row).val ∧
        ((readCell tables 61 103 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b103; omega
    · change (0 : Int) ≤ (readCell tables 61 104 row).val ∧
        ((readCell tables 61 104 row).val : Int) ≤ 255
      constructor
      · omega
      · have width := bounds.b104; omega
    · change (0 : Int) ≤ (readCell tables 61 105 row).val ∧
        ((readCell tables 61 105 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b105; omega
    · change (0 : Int) ≤ (readCell tables 61 106 row).val ∧
        ((readCell tables 61 106 row).val : Int) ≤ 16383
      constructor
      · omega
      · have width := bounds.b106; omega
    · change (0 : Int) ≤ (readCell tables 61 107 row).val ∧
        ((readCell tables 61 107 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b107; omega
    · change (0 : Int) ≤ (readCell tables 61 108 row).val ∧
        ((readCell tables 61 108 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b108; omega
    · change (0 : Int) ≤ (readCell tables 61 109 row).val ∧
        ((readCell tables 61 109 row).val : Int) ≤ 8191
      constructor
      · omega
      · have width := bounds.b109; omega
    · change (0 : Int) ≤ (readCell tables 61 110 row).val ∧
        ((readCell tables 61 110 row).val : Int) ≤ 7
      constructor
      · omega
      · have width := bounds.b110; omega
    · change (0 : Int) ≤ (readCell tables 61 111 row).val ∧
        ((readCell tables 61 111 row).val : Int) ≤ 7
      constructor
      · omega
      · have width := bounds.b111; omega
    · change (0 : Int) ≤ (readCell tables 61 112 row).val ∧
        ((readCell tables 61 112 row).val : Int) ≤ 4095
      constructor
      · omega
      · have width := bounds.b112; omega
    · change (0 : Int) ≤ (readCell tables 61 113 row).val ∧
        ((readCell tables 61 113 row).val : Int) ≤ 7
      constructor
      · omega
      · have width := bounds.b113; omega
    · change (0 : Int) ≤ (readCell tables 61 114 row).val ∧
        ((readCell tables 61 114 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b114; omega
    · change (0 : Int) ≤ (readCell tables 61 115 row).val ∧
        ((readCell tables 61 115 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b115; omega
    · change (0 : Int) ≤ (readCell tables 61 116 row).val ∧
        ((readCell tables 61 116 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b116; omega
    · change (0 : Int) ≤ (readCell tables 61 117 row).val ∧
        ((readCell tables 61 117 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b117; omega
    · change (0 : Int) ≤ (readCell tables 61 118 row).val ∧
        ((readCell tables 61 118 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b118; omega
    · change (0 : Int) ≤ (readCell tables 61 119 row).val ∧
        ((readCell tables 61 119 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b119; omega
    · change (0 : Int) ≤ (readCell tables 61 120 row).val ∧
        ((readCell tables 61 120 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b120; omega
    · change (0 : Int) ≤ (readCell tables 61 121 row).val ∧
        ((readCell tables 61 121 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b121; omega
    · change (0 : Int) ≤ (readCell tables 61 122 row).val ∧
        ((readCell tables 61 122 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
  · have missing : intervals61[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals61] using Nat.le_of_not_gt small
    simp only [columns61, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations61 (v : Nat → Int) : Prop where
  h11726 : (((1 : Int) * (v 121)) * ((((((0 : Int) + (((1 : Int) * (((((0 : Int) + (v 4)) + (v 5)) + (v 6)) + (v 7))) * ((1 : Int) - (v 33)))) + (((1 : Int) * ((65535 : Int) - (v 11))) * ((1 : Int) - (v 33)))) + (((1 : Int) * ((65535 : Int) - (v 10))) * ((1 : Int) - (v 33)))) + (((1 : Int) * ((65535 : Int) - (v 9))) * ((1 : Int) - (v 33)))) + (((1 : Int) * ((65535 : Int) - (v 8))) * ((1 : Int) - (v 33))))) = 0
  h11727 : ((((1 : Int) * (v 121)) * ((v 15) - (v 3))) * ((1 : Int) - (v 33))) = 0
  h11728 : ((((1 : Int) * (v 121)) * ((v 14) - (v 2))) * ((1 : Int) - (v 33))) = 0
  h11729 : ((((1 : Int) * (v 121)) * ((v 13) - (v 1))) * ((1 : Int) - (v 33))) = 0
  h11730 : ((((1 : Int) * (v 121)) * ((v 12) - (v 0))) * ((1 : Int) - (v 33))) = 0
  h11731 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 34)) + (((1 : Int) * (32768 : Int)) * (v 35))) - (v 11))) = 0
  h11732 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 36)) + (((1 : Int) * (16384 : Int)) * (v 37))) - (v 10))) = 0
  h11733 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 38)) + (((1 : Int) * (8192 : Int)) * (v 39))) - (v 9))) = 0
  h11734 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 40)) + (((1 : Int) * (4096 : Int)) * (v 41))) - (v 8))) = 0
  h11735 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 42) - (v 35)) - (((1 : Int) * (2 : Int)) * (v 36)))) = 0
  h11736 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 43) - (v 37)) - (((1 : Int) * (4 : Int)) * (v 38)))) = 0
  h11737 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 44) - (v 39)) - (((1 : Int) * (8 : Int)) * (v 40)))) = 0
  h11738 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 45)) + (((1 : Int) * (32768 : Int)) * (v 46))) - (v 7))) = 0
  h11739 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 47)) + (((1 : Int) * (16384 : Int)) * (v 48))) - (v 6))) = 0
  h11740 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 49)) + (((1 : Int) * (8192 : Int)) * (v 50))) - (v 5))) = 0
  h11741 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 51)) + (((1 : Int) * (4096 : Int)) * (v 52))) - (v 4))) = 0
  h11742 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 53) - (v 46)) - (((1 : Int) * (2 : Int)) * (v 47)))) = 0
  h11743 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 54) - (v 48)) - (((1 : Int) * (4 : Int)) * (v 49)))) = 0
  h11744 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 55) - (v 50)) - (((1 : Int) * (8 : Int)) * (v 51)))) = 0
  h11745 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 56)) + (((1 : Int) * (32768 : Int)) * (v 57))) - (((1 : Int) * (v 34)) * (v 45)))) = 0
  h11746 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 58)) + (((1 : Int) * (32768 : Int)) * (v 59))) - (((1 : Int) * (v 34)) * (v 53)))) = 0
  h11747 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 60)) + (((1 : Int) * (32768 : Int)) * (v 61))) - (((1 : Int) * (v 34)) * (v 54)))) = 0
  h11748 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 62)) + (((1 : Int) * (32768 : Int)) * (v 63))) - (((1 : Int) * (v 34)) * (v 55)))) = 0
  h11749 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 64)) + (((1 : Int) * (32768 : Int)) * (v 65))) - (((1 : Int) * (v 34)) * (v 52)))) = 0
  h11750 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 66)) + (((1 : Int) * (32768 : Int)) * (v 67))) - (((1 : Int) * (v 42)) * (v 45)))) = 0
  h11751 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 68)) + (((1 : Int) * (32768 : Int)) * (v 69))) - (((1 : Int) * (v 42)) * (v 53)))) = 0
  h11752 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 70)) + (((1 : Int) * (32768 : Int)) * (v 71))) - (((1 : Int) * (v 42)) * (v 54)))) = 0
  h11753 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 72)) + (((1 : Int) * (32768 : Int)) * (v 73))) - (((1 : Int) * (v 42)) * (v 55)))) = 0
  h11754 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 74)) + (((1 : Int) * (32768 : Int)) * (v 75))) - (((1 : Int) * (v 42)) * (v 52)))) = 0
  h11755 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 76)) + (((1 : Int) * (32768 : Int)) * (v 77))) - (((1 : Int) * (v 43)) * (v 45)))) = 0
  h11756 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 78)) + (((1 : Int) * (32768 : Int)) * (v 79))) - (((1 : Int) * (v 43)) * (v 53)))) = 0
  h11757 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 80)) + (((1 : Int) * (32768 : Int)) * (v 81))) - (((1 : Int) * (v 43)) * (v 54)))) = 0
  h11758 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 82)) + (((1 : Int) * (32768 : Int)) * (v 83))) - (((1 : Int) * (v 43)) * (v 55)))) = 0
  h11759 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 84)) + (((1 : Int) * (32768 : Int)) * (v 85))) - (((1 : Int) * (v 43)) * (v 52)))) = 0
  h11760 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 86)) + (((1 : Int) * (32768 : Int)) * (v 87))) - (((1 : Int) * (v 44)) * (v 45)))) = 0
  h11761 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 88)) + (((1 : Int) * (32768 : Int)) * (v 89))) - (((1 : Int) * (v 44)) * (v 53)))) = 0
  h11762 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 90)) + (((1 : Int) * (32768 : Int)) * (v 91))) - (((1 : Int) * (v 44)) * (v 54)))) = 0
  h11763 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 92)) + (((1 : Int) * (32768 : Int)) * (v 93))) - (((1 : Int) * (v 44)) * (v 55)))) = 0
  h11764 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 94)) + (((1 : Int) * (32768 : Int)) * (v 95))) - (((1 : Int) * (v 44)) * (v 52)))) = 0
  h11765 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 96)) + (((1 : Int) * (32768 : Int)) * (v 97))) - (((1 : Int) * (v 41)) * (v 45)))) = 0
  h11766 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 98)) + (((1 : Int) * (32768 : Int)) * (v 99))) - (((1 : Int) * (v 41)) * (v 53)))) = 0
  h11767 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 100)) + (((1 : Int) * (32768 : Int)) * (v 101))) - (((1 : Int) * (v 41)) * (v 54)))) = 0
  h11768 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 102)) + (((1 : Int) * (32768 : Int)) * (v 103))) - (((1 : Int) * (v 41)) * (v 55)))) = 0
  h11769 : ((((1 : Int) * (v 121)) * (v 33)) * ((v 104) - (((1 : Int) * (v 41)) * (v 52)))) = 0
  h11770 : ((((1 : Int) * (v 121)) * (v 33)) * (((((((0 : Int) + (v 105)) + (((1 : Int) * (2 : Int)) * (v 106))) + (((1 : Int) * (32768 : Int)) * (v 107))) - (v 57)) - (v 58)) - (v 66))) = 0
  h11771 : ((((1 : Int) * (v 121)) * (v 33)) * ((((((((((0 : Int) + (v 108)) + (((1 : Int) * (4 : Int)) * (v 109))) + (((1 : Int) * (32768 : Int)) * (v 110))) - (v 59)) - (v 60)) - (v 67)) - (v 68)) - (v 76)) - (v 107))) = 0
  h11772 : ((((1 : Int) * (v 121)) * (v 33)) * ((((((((((((0 : Int) + (v 111)) + (((1 : Int) * (8 : Int)) * (v 112))) + (((1 : Int) * (32768 : Int)) * (v 113))) - (v 61)) - (v 62)) - (v 69)) - (v 70)) - (v 77)) - (v 78)) - (v 86)) - (v 110))) = 0
  h11773 : ((((1 : Int) * (v 121)) * (v 33)) * (((((((((((v 114) - (v 63)) - (v 64)) - (v 71)) - (v 72)) - (v 79)) - (v 80)) - (v 87)) - (v 88)) - (v 96)) - (v 113))) = 0
  h11774 : (((1 : Int) * (v 121)) * (((((0 : Int) + (((1 : Int) * (v 33)) * (((((((((((0 : Int) + (v 65)) + (v 73)) + (v 74)) + (v 81)) + (v 82)) + (v 89)) + (v 90)) + (v 97)) + (v 98)) - (v 32)))) + (((1 : Int) * (v 33)) * (((((((((0 : Int) + (v 75)) + (v 83)) + (v 84)) + (v 91)) + (v 92)) + (v 99)) + (v 100)) - (v 32)))) + (((1 : Int) * (v 33)) * (((((((0 : Int) + (v 85)) + (v 93)) + (v 94)) + (v 101)) + (v 102)) - (v 32)))) + (((1 : Int) * (v 33)) * (((((0 : Int) + (v 95)) + (v 103)) + (v 104)) - (v 32))))) = 0
  h11775 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 23) - (v 56)) - (((1 : Int) * (32768 : Int)) * (v 105)))) = 0
  h11776 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 22) - (v 106)) - (((1 : Int) * (16384 : Int)) * (v 108)))) = 0
  h11777 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 21) - (v 109)) - (((1 : Int) * (8192 : Int)) * (v 111)))) = 0
  h11778 : ((((1 : Int) * (v 121)) * (v 33)) * (((v 20) - (v 112)) - (((1 : Int) * (4096 : Int)) * (v 114)))) = 0
  h11779 : ((((1 : Int) * (v 121)) * (v 33)) * (((((0 : Int) + (v 27)) + (((1 : Int) * (65536 : Int)) * (v 115))) - (v 23)) - (v 15))) = 0
  h11780 : ((((1 : Int) * (v 121)) * (v 33)) * ((((((0 : Int) + (v 26)) + (((1 : Int) * (65536 : Int)) * (v 116))) - (v 22)) - (v 14)) - (v 115))) = 0
  h11781 : ((((1 : Int) * (v 121)) * (v 33)) * ((((((0 : Int) + (v 25)) + (((1 : Int) * (65536 : Int)) * (v 117))) - (v 21)) - (v 13)) - (v 116))) = 0
  h11782 : ((((1 : Int) * (v 121)) * (v 33)) * ((((v 24) - (v 20)) - (v 12)) - (v 117))) = 0
  h11783 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 3)) + (((1 : Int) * (-1 : Int)) * (v 27))) - (v 32))) = 0
  h11784 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 2)) + (((1 : Int) * (-1 : Int)) * (v 26))) - (v 32))) = 0
  h11785 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 1)) + (((1 : Int) * (-1 : Int)) * (v 25))) - (v 32))) = 0
  h11786 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 0)) + (((1 : Int) * (-1 : Int)) * (v 24))) - (v 32))) = 0
  h11787 : ((((1 : Int) * (v 121)) * (v 33)) * ((((((0 : Int) + (v 31)) + (((1 : Int) * (65536 : Int)) * (v 118))) - (v 15)) - (v 19)) - (1 : Int))) = 0
  h11788 : ((((1 : Int) * (v 121)) * (v 33)) * ((((((0 : Int) + (v 30)) + (((1 : Int) * (65536 : Int)) * (v 119))) - (v 14)) - (v 18)) - (v 118))) = 0
  h11789 : ((((1 : Int) * (v 121)) * (v 33)) * ((((((0 : Int) + (v 29)) + (((1 : Int) * (65536 : Int)) * (v 120))) - (v 13)) - (v 17)) - (v 119))) = 0
  h11790 : ((((1 : Int) * (v 121)) * (v 33)) * ((((v 28) - (v 12)) - (v 16)) - (v 120))) = 0
  h11791 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 7)) + (((1 : Int) * (-1 : Int)) * (v 31))) - (v 32))) = 0
  h11792 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 6)) + (((1 : Int) * (-1 : Int)) * (v 30))) - (v 32))) = 0
  h11793 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 5)) + (((1 : Int) * (-1 : Int)) * (v 29))) - (v 32))) = 0
  h11794 : ((((1 : Int) * (v 121)) * (v 33)) * ((((0 : Int) + (v 4)) + (((1 : Int) * (-1 : Int)) * (v 28))) - (v 32))) = 0
  h11827 : ((0 : Int) - (v 32)) = 0
  h11828 : ((((1 : Int) * (v 33)) * (v 33)) - (v 33)) = 0
  h11830 : ((((1 : Int) * (v 35)) * (v 35)) - (v 35)) = 0
  h11841 : ((((1 : Int) * (v 46)) * (v 46)) - (v 46)) = 0
  h11900 : ((((1 : Int) * (v 105)) * (v 105)) - (v 105)) = 0
  h11910 : ((((1 : Int) * (v 115)) * (v 115)) - (v 115)) = 0
  h11911 : ((((1 : Int) * (v 116)) * (v 116)) - (v 116)) = 0
  h11912 : ((((1 : Int) * (v 117)) * (v 117)) - (v 117)) = 0
  h11913 : ((((1 : Int) * (v 118)) * (v 118)) - (v 118)) = 0
  h11914 : ((((1 : Int) * (v 119)) * (v 119)) - (v 119)) = 0
  h11915 : ((((1 : Int) * (v 120)) * (v 120)) - (v 120)) = 0
  h11916 : ((((1 : Int) * (v 121)) * (v 121)) - (v 121)) = 0

theorem integer_equations61 (tables : Tables) (row : Nat)
    (inside : row < (tables 61).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations61 (fun col => ((readCell tables 61 col row).val : Int)) := by
  have bounded := column_bounds61 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c11726 member11726
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11726 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11726, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11727 member11727
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11727 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11727, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11728 member11728
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11728 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11728, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11729 member11729
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11729 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11729, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11730 member11730
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11730 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11730, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11731 member11731
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11731 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11731, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11732 member11732
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11732 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11732, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11733 member11733
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11733 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11733, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11734 member11734
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11734 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11734, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11735 member11735
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11735 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11735, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11736 member11736
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11736 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11736, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11737 member11737
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11737 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11737, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11738 member11738
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11738 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11738, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11739 member11739
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11739 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11739, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11740 member11740
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11740 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11740, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11741 member11741
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11741 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11741, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11742 member11742
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11742 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11742, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11743 member11743
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11743 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11743, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11744 member11744
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11744 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11744, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11745 member11745
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11745 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11745, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11746 member11746
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11746 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11746, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11747 member11747
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11747 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11747, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11748 member11748
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11748 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11748, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11749 member11749
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11749 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11749, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11750 member11750
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11750 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11750, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11751 member11751
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11751 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11751, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11752 member11752
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11752 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11752, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11753 member11753
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11753 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11753, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11754 member11754
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11754 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11754, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11755 member11755
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11755 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11755, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11756 member11756
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11756 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11756, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11757 member11757
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11757 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11757, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11758 member11758
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11758 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11758, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11759 member11759
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11759 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11759, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11760 member11760
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11760 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11760, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11761 member11761
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11761 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11761, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11762 member11762
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11762 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11762, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11763 member11763
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11763 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11763, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11764 member11764
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11764 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11764, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11765 member11765
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11765 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11765, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11766 member11766
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11766 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11766, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11767 member11767
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11767 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11767, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11768 member11768
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11768 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11768, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11769 member11769
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11769 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11769, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11770 member11770
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11770 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11770, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11771 member11771
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11771 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11771, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11772 member11772
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11772 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11772, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11773 member11773
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11773 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11773, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11774 member11774
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11774 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11774, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11775 member11775
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11775 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11775, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11776 member11776
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11776 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11776, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11777 member11777
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11777 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11777, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11778 member11778
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11778 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11778, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11779 member11779
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11779 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11779, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11780 member11780
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11780 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11780, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11781 member11781
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11781 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11781, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11782 member11782
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11782 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11782, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11783 member11783
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11783 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11783, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11784 member11784
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11784 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11784, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11785 member11785
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11785 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11785, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11786 member11786
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11786 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11786, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11787 member11787
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11787 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11787, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11788 member11788
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11788 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11788, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11789 member11789
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11789 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11789, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11790 member11790
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11790 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11790, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11791 member11791
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11791 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11791, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11792 member11792
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11792 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11792, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11793 member11793
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11793 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11793, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11794 member11794
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11794 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11794, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11827 member11827
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11827 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11827, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11828 member11828
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11828 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11828, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11830 member11830
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11830 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11830, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11841 member11841
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11841 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11841, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11900 member11900
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11900 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11900, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11910 member11910
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11910 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11910, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11911 member11911
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11911 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11911, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11912 member11912
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11912 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11912, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11913 member11913
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11913 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11913, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11914 member11914
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11914 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11914, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11915 member11915
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11915 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11915, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11916 member11916
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11916 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 61 row columns61 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11916, Expr.evalInteger, integerConstant, fieldModulus] using lifted

def intervals62 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩
]
def columns62 (col : Nat) : Interval := intervals62[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds62 (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns62 col).Contains ((readCell tables 62 col row).val : Int) := by
  intro col
  have bound := (readCell tables 62 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 62 col row).val := by omega
  by_cases small : col < 47
  · have bounds := bounds62 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 62 0 row).val ∧
        ((readCell tables 62 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 62 1 row).val ∧
        ((readCell tables 62 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 62 2 row).val ∧
        ((readCell tables 62 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 62 3 row).val ∧
        ((readCell tables 62 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 62 4 row).val ∧
        ((readCell tables 62 4 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 62 5 row).val ∧
        ((readCell tables 62 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 62 6 row).val ∧
        ((readCell tables 62 6 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 62 7 row).val ∧
        ((readCell tables 62 7 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 62 8 row).val ∧
        ((readCell tables 62 8 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 62 9 row).val ∧
        ((readCell tables 62 9 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b9; omega
    · change (0 : Int) ≤ (readCell tables 62 10 row).val ∧
        ((readCell tables 62 10 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b10; omega
    · change (0 : Int) ≤ (readCell tables 62 11 row).val ∧
        ((readCell tables 62 11 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b11; omega
    · change (0 : Int) ≤ (readCell tables 62 12 row).val ∧
        ((readCell tables 62 12 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b12; omega
    · change (0 : Int) ≤ (readCell tables 62 13 row).val ∧
        ((readCell tables 62 13 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b13; omega
    · change (0 : Int) ≤ (readCell tables 62 14 row).val ∧
        ((readCell tables 62 14 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b14; omega
    · change (0 : Int) ≤ (readCell tables 62 15 row).val ∧
        ((readCell tables 62 15 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b15; omega
    · change (0 : Int) ≤ (readCell tables 62 16 row).val ∧
        ((readCell tables 62 16 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b16; omega
    · change (0 : Int) ≤ (readCell tables 62 17 row).val ∧
        ((readCell tables 62 17 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b17; omega
    · change (0 : Int) ≤ (readCell tables 62 18 row).val ∧
        ((readCell tables 62 18 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b18; omega
    · change (0 : Int) ≤ (readCell tables 62 19 row).val ∧
        ((readCell tables 62 19 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b19; omega
    · change (0 : Int) ≤ (readCell tables 62 20 row).val ∧
        ((readCell tables 62 20 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b20; omega
    · change (0 : Int) ≤ (readCell tables 62 21 row).val ∧
        ((readCell tables 62 21 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b21; omega
    · change (0 : Int) ≤ (readCell tables 62 22 row).val ∧
        ((readCell tables 62 22 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b22; omega
    · change (0 : Int) ≤ (readCell tables 62 23 row).val ∧
        ((readCell tables 62 23 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b23; omega
    · change (0 : Int) ≤ (readCell tables 62 24 row).val ∧
        ((readCell tables 62 24 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b24; omega
    · change (0 : Int) ≤ (readCell tables 62 25 row).val ∧
        ((readCell tables 62 25 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b25; omega
    · change (0 : Int) ≤ (readCell tables 62 26 row).val ∧
        ((readCell tables 62 26 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b26; omega
    · change (0 : Int) ≤ (readCell tables 62 27 row).val ∧
        ((readCell tables 62 27 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b27; omega
    · change (0 : Int) ≤ (readCell tables 62 28 row).val ∧
        ((readCell tables 62 28 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b28; omega
    · change (0 : Int) ≤ (readCell tables 62 29 row).val ∧
        ((readCell tables 62 29 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b29; omega
    · change (0 : Int) ≤ (readCell tables 62 30 row).val ∧
        ((readCell tables 62 30 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b30; omega
    · change (0 : Int) ≤ (readCell tables 62 31 row).val ∧
        ((readCell tables 62 31 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b31; omega
    · change (0 : Int) ≤ (readCell tables 62 32 row).val ∧
        ((readCell tables 62 32 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b32; omega
    · change (0 : Int) ≤ (readCell tables 62 33 row).val ∧
        ((readCell tables 62 33 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b33; omega
    · change (0 : Int) ≤ (readCell tables 62 34 row).val ∧
        ((readCell tables 62 34 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b34; omega
    · change (0 : Int) ≤ (readCell tables 62 35 row).val ∧
        ((readCell tables 62 35 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b35; omega
    · change (0 : Int) ≤ (readCell tables 62 36 row).val ∧
        ((readCell tables 62 36 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b36; omega
    · change (0 : Int) ≤ (readCell tables 62 37 row).val ∧
        ((readCell tables 62 37 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b37; omega
    · change (0 : Int) ≤ (readCell tables 62 38 row).val ∧
        ((readCell tables 62 38 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b38; omega
    · change (0 : Int) ≤ (readCell tables 62 39 row).val ∧
        ((readCell tables 62 39 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b39; omega
    · change (0 : Int) ≤ (readCell tables 62 40 row).val ∧
        ((readCell tables 62 40 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b40; omega
    · change (0 : Int) ≤ (readCell tables 62 41 row).val ∧
        ((readCell tables 62 41 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b41; omega
    · change (0 : Int) ≤ (readCell tables 62 42 row).val ∧
        ((readCell tables 62 42 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b42; omega
    · change (0 : Int) ≤ (readCell tables 62 43 row).val ∧
        ((readCell tables 62 43 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b43; omega
    · change (0 : Int) ≤ (readCell tables 62 44 row).val ∧
        ((readCell tables 62 44 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 62 45 row).val ∧
        ((readCell tables 62 45 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 62 46 row).val ∧
        ((readCell tables 62 46 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
  · have missing : intervals62[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals62] using Nat.le_of_not_gt small
    simp only [columns62, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations62 (v : Nat → Int) : Prop where
  h11918 : (((1 : Int) * (v 43)) * ((v 37) - (v 3))) = 0
  h11919 : (((1 : Int) * (v 43)) * ((v 36) - (v 2))) = 0
  h11920 : (((1 : Int) * (v 43)) * ((v 35) - (v 1))) = 0
  h11921 : (((1 : Int) * (v 43)) * ((((0 : Int) + (v 34)) + (((1 : Int) * (32768 : Int)) * (v 24))) - (v 0))) = 0
  h11923 : (((1 : Int) * (v 43)) * ((((((0 : Int) + (((1 : Int) * (((((0 : Int) + (v 4)) + (v 5)) + (v 6)) + (v 7))) * ((1 : Int) - (v 42)))) + (((1 : Int) * ((65535 : Int) - (v 11))) * ((1 : Int) - (v 42)))) + (((1 : Int) * ((65535 : Int) - (v 10))) * ((1 : Int) - (v 42)))) + (((1 : Int) * ((65535 : Int) - (v 9))) * ((1 : Int) - (v 42)))) + (((1 : Int) * ((65535 : Int) - (v 8))) * ((1 : Int) - (v 42))))) = 0
  h11924 : ((((1 : Int) * (v 43)) * ((v 15) - (v 3))) * ((1 : Int) - (v 42))) = 0
  h11925 : ((((1 : Int) * (v 43)) * ((v 14) - (v 2))) * ((1 : Int) - (v 42))) = 0
  h11926 : ((((1 : Int) * (v 43)) * ((v 13) - (v 1))) * ((1 : Int) - (v 42))) = 0
  h11927 : ((((1 : Int) * (v 43)) * ((v 12) - (v 0))) * ((1 : Int) - (v 42))) = 0
  h11928 : ((((1 : Int) * (v 43)) * (v 42)) * ((v 41) - (v 7))) = 0
  h11929 : ((((1 : Int) * (v 43)) * (v 42)) * ((v 40) - (v 6))) = 0
  h11930 : ((((1 : Int) * (v 43)) * (v 42)) * ((v 39) - (v 5))) = 0
  h11931 : ((((1 : Int) * (v 43)) * (v 42)) * ((((0 : Int) + (v 38)) + (((1 : Int) * (32768 : Int)) * (v 33))) - (v 4))) = 0
  h11932 : (((((1 : Int) * (v 43)) * ((1 : Int) - (((1 : Int) * ((v 24) - (v 33))) * ((v 24) - (v 33))))) * (v 42)) * ((v 11) - (v 19))) = 0
  h11933 : (((((1 : Int) * (v 43)) * ((1 : Int) - (((1 : Int) * ((v 24) - (v 33))) * ((v 24) - (v 33))))) * (v 42)) * ((v 10) - (v 18))) = 0
  h11934 : (((((1 : Int) * (v 43)) * ((1 : Int) - (((1 : Int) * ((v 24) - (v 33))) * ((v 24) - (v 33))))) * (v 42)) * ((v 9) - (v 17))) = 0
  h11935 : (((((1 : Int) * (v 43)) * ((1 : Int) - (((1 : Int) * ((v 24) - (v 33))) * ((v 24) - (v 33))))) * (v 42)) * ((v 8) - (v 16))) = 0
  h11936 : (((((1 : Int) * (v 43)) * (v 42)) * ((v 15) - (v 23))) * ((1 : Int) - (v 24))) = 0
  h11937 : (((((1 : Int) * (v 43)) * (v 42)) * ((v 14) - (v 22))) * ((1 : Int) - (v 24))) = 0
  h11938 : (((((1 : Int) * (v 43)) * (v 42)) * ((v 13) - (v 21))) * ((1 : Int) - (v 24))) = 0
  h11939 : (((((1 : Int) * (v 43)) * (v 42)) * ((v 12) - (v 20))) * ((1 : Int) - (v 24))) = 0
  h11964 : ((((1 : Int) * (v 24)) * (v 24)) - (v 24)) = 0
  h11973 : ((((1 : Int) * (v 33)) * (v 33)) - (v 33)) = 0
  h11982 : ((((1 : Int) * (v 42)) * (v 42)) - (v 42)) = 0
  h11983 : ((((1 : Int) * (v 43)) * (v 43)) - (v 43)) = 0
  h11987 : (((((1 : Int) * ((v 24) - (v 33))) * (v 42)) * (v 43)) * ((1 : Int) - (v 44))) = 0

theorem integer_equations62 (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations62 (fun col => ((readCell tables 62 col row).val : Int)) := by
  have bounded := column_bounds62 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c11918 member11918
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11918 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11918, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11919 member11919
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11919 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11919, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11920 member11920
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11920 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11920, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11921 member11921
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11921 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11921, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11923 member11923
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11923 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11923, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11924 member11924
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11924 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11924, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11925 member11925
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11925 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11925, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11926 member11926
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11926 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11926, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11927 member11927
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11927 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11927, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11928 member11928
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11928 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11928, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11929 member11929
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11929 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11929, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11930 member11930
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11930 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11930, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11931 member11931
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11931 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11931, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11932 member11932
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11932 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11932, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11933 member11933
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11933 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11933, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11934 member11934
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11934 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11934, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11935 member11935
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11935 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11935, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11936 member11936
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11936 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11936, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11937 member11937
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11937 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11937, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11938 member11938
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11938 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11938, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11939 member11939
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11939 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11939, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11964 member11964
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11964 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11964, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11973 member11973
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11973 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11973, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11982 member11982
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11982 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11982, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11983 member11983
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11983 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11983, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11987 member11987
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11987 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 62 row columns62 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11987, Expr.evalInteger, integerConstant, fieldModulus] using lifted

def intervals63 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 0⟩,
  ⟨0, 1⟩,
  ⟨0, 32767⟩,
  ⟨0, 1⟩,
  ⟨0, 16383⟩,
  ⟨0, 3⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 1⟩,
  ⟨0, 16383⟩,
  ⟨0, 3⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 3⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 32767⟩,
  ⟨0, 3⟩,
  ⟨0, 32767⟩,
  ⟨0, 3⟩,
  ⟨0, 32767⟩,
  ⟨0, 3⟩,
  ⟨0, 15⟩,
  ⟨0, 1⟩,
  ⟨0, 16383⟩,
  ⟨0, 3⟩,
  ⟨0, 3⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 2130706432⟩
]
def columns63 (col : Nat) : Interval := intervals63[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds63 (tables : Tables) (row : Nat)
    (inside : row < (tables 63).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns63 col).Contains ((readCell tables 63 col row).val : Int) := by
  intro col
  have bound := (readCell tables 63 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 63 col row).val := by omega
  by_cases small : col < 53
  · have bounds := bounds63 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 63 0 row).val ∧
        ((readCell tables 63 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 63 1 row).val ∧
        ((readCell tables 63 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 63 2 row).val ∧
        ((readCell tables 63 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 63 3 row).val ∧
        ((readCell tables 63 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 63 4 row).val ∧
        ((readCell tables 63 4 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 63 5 row).val ∧
        ((readCell tables 63 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 63 6 row).val ∧
        ((readCell tables 63 6 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 63 7 row).val ∧
        ((readCell tables 63 7 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 63 8 row).val ∧
        ((readCell tables 63 8 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 63 9 row).val ∧
        ((readCell tables 63 9 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b9; omega
    · change (0 : Int) ≤ (readCell tables 63 10 row).val ∧
        ((readCell tables 63 10 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b10; omega
    · change (0 : Int) ≤ (readCell tables 63 11 row).val ∧
        ((readCell tables 63 11 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b11; omega
    · change (0 : Int) ≤ (readCell tables 63 12 row).val ∧
        ((readCell tables 63 12 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b12; omega
    · change (0 : Int) ≤ (readCell tables 63 13 row).val ∧
        ((readCell tables 63 13 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b13; omega
    · change (0 : Int) ≤ (readCell tables 63 14 row).val ∧
        ((readCell tables 63 14 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b14; omega
    · change (0 : Int) ≤ (readCell tables 63 15 row).val ∧
        ((readCell tables 63 15 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b15; omega
    · change (0 : Int) ≤ (readCell tables 63 16 row).val ∧
        ((readCell tables 63 16 row).val : Int) ≤ 0
      constructor
      · omega
      · have width := bounds.b16; omega
    · change (0 : Int) ≤ (readCell tables 63 17 row).val ∧
        ((readCell tables 63 17 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b17; omega
    · change (0 : Int) ≤ (readCell tables 63 18 row).val ∧
        ((readCell tables 63 18 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b18; omega
    · change (0 : Int) ≤ (readCell tables 63 19 row).val ∧
        ((readCell tables 63 19 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b19; omega
    · change (0 : Int) ≤ (readCell tables 63 20 row).val ∧
        ((readCell tables 63 20 row).val : Int) ≤ 16383
      constructor
      · omega
      · have width := bounds.b20; omega
    · change (0 : Int) ≤ (readCell tables 63 21 row).val ∧
        ((readCell tables 63 21 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b21; omega
    · change (0 : Int) ≤ (readCell tables 63 22 row).val ∧
        ((readCell tables 63 22 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b22; omega
    · change (0 : Int) ≤ (readCell tables 63 23 row).val ∧
        ((readCell tables 63 23 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b23; omega
    · change (0 : Int) ≤ (readCell tables 63 24 row).val ∧
        ((readCell tables 63 24 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b24; omega
    · change (0 : Int) ≤ (readCell tables 63 25 row).val ∧
        ((readCell tables 63 25 row).val : Int) ≤ 16383
      constructor
      · omega
      · have width := bounds.b25; omega
    · change (0 : Int) ≤ (readCell tables 63 26 row).val ∧
        ((readCell tables 63 26 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b26; omega
    · change (0 : Int) ≤ (readCell tables 63 27 row).val ∧
        ((readCell tables 63 27 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b27; omega
    · change (0 : Int) ≤ (readCell tables 63 28 row).val ∧
        ((readCell tables 63 28 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b28; omega
    · change (0 : Int) ≤ (readCell tables 63 29 row).val ∧
        ((readCell tables 63 29 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b29; omega
    · change (0 : Int) ≤ (readCell tables 63 30 row).val ∧
        ((readCell tables 63 30 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b30; omega
    · change (0 : Int) ≤ (readCell tables 63 31 row).val ∧
        ((readCell tables 63 31 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b31; omega
    · change (0 : Int) ≤ (readCell tables 63 32 row).val ∧
        ((readCell tables 63 32 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b32; omega
    · change (0 : Int) ≤ (readCell tables 63 33 row).val ∧
        ((readCell tables 63 33 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b33; omega
    · change (0 : Int) ≤ (readCell tables 63 34 row).val ∧
        ((readCell tables 63 34 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b34; omega
    · change (0 : Int) ≤ (readCell tables 63 35 row).val ∧
        ((readCell tables 63 35 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b35; omega
    · change (0 : Int) ≤ (readCell tables 63 36 row).val ∧
        ((readCell tables 63 36 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b36; omega
    · change (0 : Int) ≤ (readCell tables 63 37 row).val ∧
        ((readCell tables 63 37 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b37; omega
    · change (0 : Int) ≤ (readCell tables 63 38 row).val ∧
        ((readCell tables 63 38 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b38; omega
    · change (0 : Int) ≤ (readCell tables 63 39 row).val ∧
        ((readCell tables 63 39 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b39; omega
    · change (0 : Int) ≤ (readCell tables 63 40 row).val ∧
        ((readCell tables 63 40 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b40; omega
    · change (0 : Int) ≤ (readCell tables 63 41 row).val ∧
        ((readCell tables 63 41 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b41; omega
    · change (0 : Int) ≤ (readCell tables 63 42 row).val ∧
        ((readCell tables 63 42 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b42; omega
    · change (0 : Int) ≤ (readCell tables 63 43 row).val ∧
        ((readCell tables 63 43 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b43; omega
    · change (0 : Int) ≤ (readCell tables 63 44 row).val ∧
        ((readCell tables 63 44 row).val : Int) ≤ 15
      constructor
      · omega
      · have width := bounds.b44; omega
    · change (0 : Int) ≤ (readCell tables 63 45 row).val ∧
        ((readCell tables 63 45 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b45; omega
    · change (0 : Int) ≤ (readCell tables 63 46 row).val ∧
        ((readCell tables 63 46 row).val : Int) ≤ 16383
      constructor
      · omega
      · have width := bounds.b46; omega
    · change (0 : Int) ≤ (readCell tables 63 47 row).val ∧
        ((readCell tables 63 47 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b47; omega
    · change (0 : Int) ≤ (readCell tables 63 48 row).val ∧
        ((readCell tables 63 48 row).val : Int) ≤ 3
      constructor
      · omega
      · have width := bounds.b48; omega
    · change (0 : Int) ≤ (readCell tables 63 49 row).val ∧
        ((readCell tables 63 49 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b49; omega
    · change (0 : Int) ≤ (readCell tables 63 50 row).val ∧
        ((readCell tables 63 50 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b50; omega
    · change (0 : Int) ≤ (readCell tables 63 51 row).val ∧
        ((readCell tables 63 51 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b51; omega
    · change (0 : Int) ≤ (readCell tables 63 52 row).val ∧
        ((readCell tables 63 52 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
  · have missing : intervals63[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals63] using Nat.le_of_not_gt small
    simp only [columns63, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations63 (v : Nat → Int) : Prop where
  h11994 : (((1 : Int) * (v 51)) * ((((0 : Int) + (((1 : Int) * (((0 : Int) + (v 2)) + (v 3))) * ((1 : Int) - (v 17)))) + (((1 : Int) * ((65535 : Int) - (v 5))) * ((1 : Int) - (v 17)))) + (((1 : Int) * ((65535 : Int) - (v 4))) * ((1 : Int) - (v 17))))) = 0
  h11995 : ((((1 : Int) * (v 51)) * ((v 7) - (v 1))) * ((1 : Int) - (v 17))) = 0
  h11996 : ((((1 : Int) * (v 51)) * ((v 6) - (v 0))) * ((1 : Int) - (v 17))) = 0
  h11997 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 18)) + (((1 : Int) * (32768 : Int)) * (v 19))) - (v 5))) = 0
  h11998 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 20)) + (((1 : Int) * (16384 : Int)) * (v 21))) - (v 4))) = 0
  h11999 : ((((1 : Int) * (v 51)) * (v 17)) * (((v 22) - (v 19)) - (((1 : Int) * (2 : Int)) * (v 20)))) = 0
  h12000 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 23)) + (((1 : Int) * (32768 : Int)) * (v 24))) - (v 3))) = 0
  h12001 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 25)) + (((1 : Int) * (16384 : Int)) * (v 26))) - (v 2))) = 0
  h12002 : ((((1 : Int) * (v 51)) * (v 17)) * (((v 27) - (v 24)) - (((1 : Int) * (2 : Int)) * (v 25)))) = 0
  h12003 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 28)) + (((1 : Int) * (32768 : Int)) * (v 29))) - (((1 : Int) * (v 18)) * (v 23)))) = 0
  h12004 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 30)) + (((1 : Int) * (32768 : Int)) * (v 31))) - (((1 : Int) * (v 18)) * (v 27)))) = 0
  h12005 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 32)) + (((1 : Int) * (32768 : Int)) * (v 33))) - (((1 : Int) * (v 18)) * (v 26)))) = 0
  h12006 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 34)) + (((1 : Int) * (32768 : Int)) * (v 35))) - (((1 : Int) * (v 22)) * (v 23)))) = 0
  h12007 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 36)) + (((1 : Int) * (32768 : Int)) * (v 37))) - (((1 : Int) * (v 22)) * (v 27)))) = 0
  h12008 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 38)) + (((1 : Int) * (32768 : Int)) * (v 39))) - (((1 : Int) * (v 22)) * (v 26)))) = 0
  h12009 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 40)) + (((1 : Int) * (32768 : Int)) * (v 41))) - (((1 : Int) * (v 21)) * (v 23)))) = 0
  h12010 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 42)) + (((1 : Int) * (32768 : Int)) * (v 43))) - (((1 : Int) * (v 21)) * (v 27)))) = 0
  h12011 : ((((1 : Int) * (v 51)) * (v 17)) * ((v 44) - (((1 : Int) * (v 21)) * (v 26)))) = 0
  h12012 : ((((1 : Int) * (v 51)) * (v 17)) * (((((((0 : Int) + (v 45)) + (((1 : Int) * (2 : Int)) * (v 46))) + (((1 : Int) * (32768 : Int)) * (v 47))) - (v 29)) - (v 30)) - (v 34))) = 0
  h12013 : ((((1 : Int) * (v 51)) * (v 17)) * (((((((v 48) - (v 31)) - (v 32)) - (v 35)) - (v 36)) - (v 40)) - (v 47))) = 0
  h12014 : (((1 : Int) * (v 51)) * (((0 : Int) + (((1 : Int) * (v 17)) * (((((((0 : Int) + (v 33)) + (v 37)) + (v 38)) + (v 41)) + (v 42)) - (v 16)))) + (((1 : Int) * (v 17)) * (((((0 : Int) + (v 39)) + (v 43)) + (v 44)) - (v 16))))) = 0
  h12015 : ((((1 : Int) * (v 51)) * (v 17)) * (((v 11) - (v 28)) - (((1 : Int) * (32768 : Int)) * (v 45)))) = 0
  h12016 : ((((1 : Int) * (v 51)) * (v 17)) * (((v 10) - (v 46)) - (((1 : Int) * (16384 : Int)) * (v 48)))) = 0
  h12017 : ((((1 : Int) * (v 51)) * (v 17)) * (((((0 : Int) + (v 13)) + (((1 : Int) * (65536 : Int)) * (v 49))) - (v 11)) - (v 7))) = 0
  h12018 : ((((1 : Int) * (v 51)) * (v 17)) * ((((v 12) - (v 10)) - (v 6)) - (v 49))) = 0
  h12019 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 1)) + (((1 : Int) * (-1 : Int)) * (v 13))) - (v 16))) = 0
  h12020 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 0)) + (((1 : Int) * (-1 : Int)) * (v 12))) - (v 16))) = 0
  h12021 : ((((1 : Int) * (v 51)) * (v 17)) * ((((((0 : Int) + (v 15)) + (((1 : Int) * (65536 : Int)) * (v 50))) - (v 7)) - (v 9)) - (1 : Int))) = 0
  h12022 : ((((1 : Int) * (v 51)) * (v 17)) * ((((v 14) - (v 6)) - (v 8)) - (v 50))) = 0
  h12023 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 3)) + (((1 : Int) * (-1 : Int)) * (v 15))) - (v 16))) = 0
  h12024 : ((((1 : Int) * (v 51)) * (v 17)) * ((((0 : Int) + (v 2)) + (((1 : Int) * (-1 : Int)) * (v 14))) - (v 16))) = 0
  h12041 : ((0 : Int) - (v 16)) = 0
  h12042 : ((((1 : Int) * (v 17)) * (v 17)) - (v 17)) = 0
  h12044 : ((((1 : Int) * (v 19)) * (v 19)) - (v 19)) = 0
  h12049 : ((((1 : Int) * (v 24)) * (v 24)) - (v 24)) = 0
  h12070 : ((((1 : Int) * (v 45)) * (v 45)) - (v 45)) = 0
  h12074 : ((((1 : Int) * (v 49)) * (v 49)) - (v 49)) = 0
  h12075 : ((((1 : Int) * (v 50)) * (v 50)) - (v 50)) = 0
  h12076 : ((((1 : Int) * (v 51)) * (v 51)) - (v 51)) = 0

theorem integer_equations63 (tables : Tables) (row : Nat)
    (inside : row < (tables 63).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations63 (fun col => ((readCell tables 63 col row).val : Int)) := by
  have bounded := column_bounds63 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c11994 member11994
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11994 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11994, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11995 member11995
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11995 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11995, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11996 member11996
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11996 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11996, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11997 member11997
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11997 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11997, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11998 member11998
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11998 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11998, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c11999 member11999
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c11999 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c11999, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12000 member12000
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12000 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12000, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12001 member12001
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12001 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12001, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12002 member12002
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12002 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12002, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12003 member12003
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12003 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12003, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12004 member12004
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12004 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12004, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12005 member12005
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12005 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12005, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12006 member12006
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12006 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12006, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12007 member12007
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12007 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12007, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12008 member12008
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12008 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12008, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12009 member12009
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12009 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12009, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12010 member12010
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12010 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12010, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12011 member12011
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12011 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12011, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12012 member12012
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12012 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12012, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12013 member12013
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12013 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12013, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12014 member12014
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12014 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12014, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12015 member12015
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12015 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12015, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12016 member12016
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12016 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12016, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12017 member12017
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12017 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12017, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12018 member12018
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12018 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12018, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12019 member12019
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12019 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12019, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12020 member12020
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12020 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12020, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12021 member12021
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12021 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12021, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12022 member12022
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12022 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12022, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12023 member12023
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12023 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12023, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12024 member12024
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12024 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12024, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12041 member12041
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12041 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12041, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12042 member12042
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12042 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12042, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12044 member12044
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12044 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12044, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12049 member12049
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12049 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12049, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12070 member12070
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12070 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12070, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12074 member12074
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12074 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12074, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12075 member12075
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12075 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12075, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12076 member12076
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12076 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 63 row columns63 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12076, Expr.evalInteger, integerConstant, fieldModulus] using lifted

def intervals64 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩
]
def columns64 (col : Nat) : Interval := intervals64[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds64 (tables : Tables) (row : Nat)
    (inside : row < (tables 64).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns64 col).Contains ((readCell tables 64 col row).val : Int) := by
  intro col
  have bound := (readCell tables 64 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 64 col row).val := by omega
  by_cases small : col < 27
  · have bounds := bounds64 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 64 0 row).val ∧
        ((readCell tables 64 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 64 1 row).val ∧
        ((readCell tables 64 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 64 2 row).val ∧
        ((readCell tables 64 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 64 3 row).val ∧
        ((readCell tables 64 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 64 4 row).val ∧
        ((readCell tables 64 4 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 64 5 row).val ∧
        ((readCell tables 64 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 64 6 row).val ∧
        ((readCell tables 64 6 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 64 7 row).val ∧
        ((readCell tables 64 7 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 64 8 row).val ∧
        ((readCell tables 64 8 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 64 9 row).val ∧
        ((readCell tables 64 9 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b9; omega
    · change (0 : Int) ≤ (readCell tables 64 10 row).val ∧
        ((readCell tables 64 10 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b10; omega
    · change (0 : Int) ≤ (readCell tables 64 11 row).val ∧
        ((readCell tables 64 11 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b11; omega
    · change (0 : Int) ≤ (readCell tables 64 12 row).val ∧
        ((readCell tables 64 12 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b12; omega
    · change (0 : Int) ≤ (readCell tables 64 13 row).val ∧
        ((readCell tables 64 13 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b13; omega
    · change (0 : Int) ≤ (readCell tables 64 14 row).val ∧
        ((readCell tables 64 14 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b14; omega
    · change (0 : Int) ≤ (readCell tables 64 15 row).val ∧
        ((readCell tables 64 15 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b15; omega
    · change (0 : Int) ≤ (readCell tables 64 16 row).val ∧
        ((readCell tables 64 16 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b16; omega
    · change (0 : Int) ≤ (readCell tables 64 17 row).val ∧
        ((readCell tables 64 17 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b17; omega
    · change (0 : Int) ≤ (readCell tables 64 18 row).val ∧
        ((readCell tables 64 18 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b18; omega
    · change (0 : Int) ≤ (readCell tables 64 19 row).val ∧
        ((readCell tables 64 19 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b19; omega
    · change (0 : Int) ≤ (readCell tables 64 20 row).val ∧
        ((readCell tables 64 20 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b20; omega
    · change (0 : Int) ≤ (readCell tables 64 21 row).val ∧
        ((readCell tables 64 21 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b21; omega
    · change (0 : Int) ≤ (readCell tables 64 22 row).val ∧
        ((readCell tables 64 22 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b22; omega
    · change (0 : Int) ≤ (readCell tables 64 23 row).val ∧
        ((readCell tables 64 23 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b23; omega
    · change (0 : Int) ≤ (readCell tables 64 24 row).val ∧
        ((readCell tables 64 24 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 64 25 row).val ∧
        ((readCell tables 64 25 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 64 26 row).val ∧
        ((readCell tables 64 26 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
  · have missing : intervals64[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals64] using Nat.le_of_not_gt small
    simp only [columns64, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations64 (v : Nat → Int) : Prop where
  h12078 : (((1 : Int) * (v 23)) * ((v 19) - (v 1))) = 0
  h12079 : (((1 : Int) * (v 23)) * ((((0 : Int) + (v 18)) + (((1 : Int) * (32768 : Int)) * (v 12))) - (v 0))) = 0
  h12081 : (((1 : Int) * (v 23)) * ((((0 : Int) + (((1 : Int) * (((0 : Int) + (v 2)) + (v 3))) * ((1 : Int) - (v 22)))) + (((1 : Int) * ((65535 : Int) - (v 5))) * ((1 : Int) - (v 22)))) + (((1 : Int) * ((65535 : Int) - (v 4))) * ((1 : Int) - (v 22))))) = 0
  h12082 : ((((1 : Int) * (v 23)) * ((v 7) - (v 1))) * ((1 : Int) - (v 22))) = 0
  h12083 : ((((1 : Int) * (v 23)) * ((v 6) - (v 0))) * ((1 : Int) - (v 22))) = 0
  h12084 : ((((1 : Int) * (v 23)) * (v 22)) * ((v 21) - (v 3))) = 0
  h12085 : ((((1 : Int) * (v 23)) * (v 22)) * ((((0 : Int) + (v 20)) + (((1 : Int) * (32768 : Int)) * (v 17))) - (v 2))) = 0
  h12086 : (((((1 : Int) * (v 23)) * ((1 : Int) - (((1 : Int) * ((v 12) - (v 17))) * ((v 12) - (v 17))))) * (v 22)) * ((v 5) - (v 9))) = 0
  h12087 : (((((1 : Int) * (v 23)) * ((1 : Int) - (((1 : Int) * ((v 12) - (v 17))) * ((v 12) - (v 17))))) * (v 22)) * ((v 4) - (v 8))) = 0
  h12088 : (((((1 : Int) * (v 23)) * (v 22)) * ((v 7) - (v 11))) * ((1 : Int) - (v 12))) = 0
  h12089 : (((((1 : Int) * (v 23)) * (v 22)) * ((v 6) - (v 10))) * ((1 : Int) - (v 12))) = 0
  h12102 : ((((1 : Int) * (v 12)) * (v 12)) - (v 12)) = 0
  h12107 : ((((1 : Int) * (v 17)) * (v 17)) - (v 17)) = 0
  h12112 : ((((1 : Int) * (v 22)) * (v 22)) - (v 22)) = 0
  h12113 : ((((1 : Int) * (v 23)) * (v 23)) - (v 23)) = 0
  h12117 : (((((1 : Int) * ((v 12) - (v 17))) * (v 22)) * (v 23)) * ((1 : Int) - (v 24))) = 0

theorem integer_equations64 (tables : Tables) (row : Nat)
    (inside : row < (tables 64).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations64 (fun col => ((readCell tables 64 col row).val : Int)) := by
  have bounded := column_bounds64 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c12078 member12078
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12078 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12078, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12079 member12079
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12079 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12079, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12081 member12081
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12081 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12081, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12082 member12082
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12082 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12082, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12083 member12083
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12083 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12083, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12084 member12084
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12084 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12084, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12085 member12085
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12085 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12085, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12086 member12086
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12086 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12086, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12087 member12087
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12087 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12087, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12088 member12088
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12088 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12088, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12089 member12089
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12089 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12089, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12102 member12102
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12102 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12102, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12107 member12107
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12107 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12107, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12112 member12112
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12112 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12112, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12113 member12113
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12113 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12113, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12117 member12117
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12117 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 64 row columns64 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12117, Expr.evalInteger, integerConstant, fieldModulus] using lifted

def intervals65 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 2130706432⟩
]
def columns65 (col : Nat) : Interval := intervals65[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds65 (tables : Tables) (row : Nat)
    (inside : row < (tables 65).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns65 col).Contains ((readCell tables 65 col row).val : Int) := by
  intro col
  have bound := (readCell tables 65 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 65 col row).val := by omega
  by_cases small : col < 30
  · have bounds := bounds65 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 65 0 row).val ∧
        ((readCell tables 65 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 65 1 row).val ∧
        ((readCell tables 65 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 65 2 row).val ∧
        ((readCell tables 65 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 65 3 row).val ∧
        ((readCell tables 65 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 65 4 row).val ∧
        ((readCell tables 65 4 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 65 5 row).val ∧
        ((readCell tables 65 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 65 6 row).val ∧
        ((readCell tables 65 6 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 65 7 row).val ∧
        ((readCell tables 65 7 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 65 8 row).val ∧
        ((readCell tables 65 8 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 65 9 row).val ∧
        ((readCell tables 65 9 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b9; omega
    · change (0 : Int) ≤ (readCell tables 65 10 row).val ∧
        ((readCell tables 65 10 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b10; omega
    · change (0 : Int) ≤ (readCell tables 65 11 row).val ∧
        ((readCell tables 65 11 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b11; omega
    · change (0 : Int) ≤ (readCell tables 65 12 row).val ∧
        ((readCell tables 65 12 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b12; omega
    · change (0 : Int) ≤ (readCell tables 65 13 row).val ∧
        ((readCell tables 65 13 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b13; omega
    · change (0 : Int) ≤ (readCell tables 65 14 row).val ∧
        ((readCell tables 65 14 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b14; omega
    · change (0 : Int) ≤ (readCell tables 65 15 row).val ∧
        ((readCell tables 65 15 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b15; omega
    · change (0 : Int) ≤ (readCell tables 65 16 row).val ∧
        ((readCell tables 65 16 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b16; omega
    · change (0 : Int) ≤ (readCell tables 65 17 row).val ∧
        ((readCell tables 65 17 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b17; omega
    · change (0 : Int) ≤ (readCell tables 65 18 row).val ∧
        ((readCell tables 65 18 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b18; omega
    · change (0 : Int) ≤ (readCell tables 65 19 row).val ∧
        ((readCell tables 65 19 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b19; omega
    · change (0 : Int) ≤ (readCell tables 65 20 row).val ∧
        ((readCell tables 65 20 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b20; omega
    · change (0 : Int) ≤ (readCell tables 65 21 row).val ∧
        ((readCell tables 65 21 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b21; omega
    · change (0 : Int) ≤ (readCell tables 65 22 row).val ∧
        ((readCell tables 65 22 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b22; omega
    · change (0 : Int) ≤ (readCell tables 65 23 row).val ∧
        ((readCell tables 65 23 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b23; omega
    · change (0 : Int) ≤ (readCell tables 65 24 row).val ∧
        ((readCell tables 65 24 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b24; omega
    · change (0 : Int) ≤ (readCell tables 65 25 row).val ∧
        ((readCell tables 65 25 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b25; omega
    · change (0 : Int) ≤ (readCell tables 65 26 row).val ∧
        ((readCell tables 65 26 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b26; omega
    · change (0 : Int) ≤ (readCell tables 65 27 row).val ∧
        ((readCell tables 65 27 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b27; omega
    · change (0 : Int) ≤ (readCell tables 65 28 row).val ∧
        ((readCell tables 65 28 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b28; omega
    · change (0 : Int) ≤ (readCell tables 65 29 row).val ∧
        ((readCell tables 65 29 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
  · have missing : intervals65[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals65] using Nat.le_of_not_gt small
    simp only [columns65, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations65 (v : Nat → Int) : Prop where
  h12123 : (((1 : Int) * (v 28)) * ((v 20) - (v 3))) = 0
  h12124 : (((1 : Int) * (v 28)) * ((v 19) - (v 2))) = 0
  h12125 : (((1 : Int) * (v 28)) * ((v 18) - (v 1))) = 0
  h12126 : (((1 : Int) * (v 28)) * ((((0 : Int) + (v 17)) + (((1 : Int) * (32768 : Int)) * (v 8))) - (v 0))) = 0
  h12128 : (((1 : Int) * (v 28)) * ((((((((((0 : Int) + (((1 : Int) * (((((0 : Int) + (v 0)) + (v 1)) + (v 2)) + (v 3))) * ((1 : Int) - (v 21)))) + (((1 : Int) * (v 7)) * ((1 : Int) - (v 21)))) + (((1 : Int) * (v 6)) * ((1 : Int) - (v 21)))) + (((1 : Int) * (v 5)) * ((1 : Int) - (v 21)))) + (((1 : Int) * (v 4)) * ((1 : Int) - (v 21)))) + ((((1 : Int) * (v 21)) * ((65535 : Int) - (v 12))) * ((1 : Int) - (v 8)))) + ((((1 : Int) * (v 21)) * ((65535 : Int) - (v 11))) * ((1 : Int) - (v 8)))) + ((((1 : Int) * (v 21)) * ((65535 : Int) - (v 10))) * ((1 : Int) - (v 8)))) + ((((1 : Int) * (v 21)) * ((65535 : Int) - (v 9))) * ((1 : Int) - (v 8))))) = 0
  h12129 : (((((1 : Int) * (v 28)) * (v 21)) * (((((0 : Int) + (v 3)) + (-1 : Int)) + (((1 : Int) * (65536 : Int)) * (v 22))) - (v 16))) * ((1 : Int) - (v 8))) = 0
  h12130 : (((((1 : Int) * (v 28)) * (v 21)) * ((((v 15) - (v 2)) - (((1 : Int) * (-1 : Int)) * (v 22))) - (((1 : Int) * (65536 : Int)) * (v 23)))) * ((1 : Int) - (v 8))) = 0
  h12131 : (((((1 : Int) * (v 28)) * (v 21)) * ((((v 14) - (v 1)) - (((1 : Int) * (-1 : Int)) * (v 23))) - (((1 : Int) * (65536 : Int)) * (v 24)))) * ((1 : Int) - (v 8))) = 0
  h12132 : (((((1 : Int) * (v 28)) * (v 21)) * (((v 13) - (v 0)) - (((1 : Int) * (-1 : Int)) * (v 24)))) * ((1 : Int) - (v 8))) = 0
  h12133 : (((((1 : Int) * (v 28)) * (v 21)) * ((((v 7) - (v 12)) - (((1 : Int) * (-1 : Int)) * (v 16))) - (((1 : Int) * (65536 : Int)) * (v 25)))) * ((1 : Int) - (v 8))) = 0
  h12134 : (((((1 : Int) * (v 28)) * (v 21)) * (((((v 6) - (v 11)) - (((1 : Int) * (-1 : Int)) * (v 15))) - (((1 : Int) * (-1 : Int)) * (v 25))) - (((1 : Int) * (65536 : Int)) * (v 26)))) * ((1 : Int) - (v 8))) = 0
  h12135 : (((((1 : Int) * (v 28)) * (v 21)) * (((((v 5) - (v 10)) - (((1 : Int) * (-1 : Int)) * (v 14))) - (((1 : Int) * (-1 : Int)) * (v 26))) - (((1 : Int) * (65536 : Int)) * (v 27)))) * ((1 : Int) - (v 8))) = 0
  h12136 : (((((1 : Int) * (v 28)) * (v 21)) * ((((v 4) - (v 9)) - (((1 : Int) * (-1 : Int)) * (v 13))) - (((1 : Int) * (-1 : Int)) * (v 27)))) * ((1 : Int) - (v 8))) = 0
  h12137 : (((1 : Int) * (v 28)) * (((((0 : Int) + ((((1 : Int) * (v 8)) * (v 21)) * ((65535 : Int) - (v 16)))) + ((((1 : Int) * (v 8)) * (v 21)) * ((65535 : Int) - (v 15)))) + ((((1 : Int) * (v 8)) * (v 21)) * ((65535 : Int) - (v 14)))) + ((((1 : Int) * (v 8)) * (v 21)) * ((65535 : Int) - (v 13))))) = 0
  h12138 : (((((1 : Int) * (v 28)) * (v 8)) * (v 21)) * ((((v 12) - (v 16)) - (((1 : Int) * (-1 : Int)) * (v 3))) - (((1 : Int) * (65536 : Int)) * (v 22)))) = 0
  h12139 : (((((1 : Int) * (v 28)) * (v 8)) * (v 21)) * (((((v 11) - (v 15)) - (((1 : Int) * (-1 : Int)) * (v 2))) - (((1 : Int) * (-1 : Int)) * (v 22))) - (((1 : Int) * (65536 : Int)) * (v 23)))) = 0
  h12140 : (((((1 : Int) * (v 28)) * (v 8)) * (v 21)) * (((((v 10) - (v 14)) - (((1 : Int) * (-1 : Int)) * (v 1))) - (((1 : Int) * (-1 : Int)) * (v 23))) - (((1 : Int) * (65536 : Int)) * (v 24)))) = 0
  h12141 : (((((1 : Int) * (v 28)) * (v 8)) * (v 21)) * ((((v 9) - (v 13)) - (((1 : Int) * (-1 : Int)) * (v 0))) - (((1 : Int) * (-1 : Int)) * (v 24)))) = 0
  h12142 : (((((1 : Int) * (v 28)) * (v 8)) * (v 21)) * (((((0 : Int) + (v 7)) + (((1 : Int) * (65536 : Int)) * (v 25))) - (v 12)) - (1 : Int))) = 0
  h12143 : (((((1 : Int) * (v 28)) * (v 8)) * (v 21)) * (((((0 : Int) + (v 6)) + (((1 : Int) * (65536 : Int)) * (v 26))) - (v 11)) - (v 25))) = 0
  h12144 : (((((1 : Int) * (v 28)) * (v 8)) * (v 21)) * (((((0 : Int) + (v 5)) + (((1 : Int) * (65536 : Int)) * (v 27))) - (v 10)) - (v 26))) = 0
  h12145 : (((((1 : Int) * (v 28)) * (v 8)) * (v 21)) * (((v 4) - (v 9)) - (v 27))) = 0
  h12154 : ((((1 : Int) * (v 8)) * (v 8)) - (v 8)) = 0
  h12167 : ((((1 : Int) * (v 21)) * (v 21)) - (v 21)) = 0
  h12168 : ((((1 : Int) * (v 22)) * (v 22)) - (v 22)) = 0
  h12169 : ((((1 : Int) * (v 23)) * (v 23)) - (v 23)) = 0
  h12170 : ((((1 : Int) * (v 24)) * (v 24)) - (v 24)) = 0
  h12171 : ((((1 : Int) * (v 25)) * (v 25)) - (v 25)) = 0
  h12172 : ((((1 : Int) * (v 26)) * (v 26)) - (v 26)) = 0
  h12173 : ((((1 : Int) * (v 27)) * (v 27)) - (v 27)) = 0
  h12174 : ((((1 : Int) * (v 28)) * (v 28)) - (v 28)) = 0

theorem integer_equations65 (tables : Tables) (row : Nat)
    (inside : row < (tables 65).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations65 (fun col => ((readCell tables 65 col row).val : Int)) := by
  have bounded := column_bounds65 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c12123 member12123
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12123 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12123, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12124 member12124
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12124 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12124, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12125 member12125
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12125 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12125, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12126 member12126
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12126 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12126, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12128 member12128
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12128 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12128, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12129 member12129
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12129 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12129, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12130 member12130
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12130 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12130, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12131 member12131
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12131 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12131, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12132 member12132
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12132 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12132, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12133 member12133
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12133 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12133, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12134 member12134
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12134 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12134, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12135 member12135
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12135 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12135, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12136 member12136
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12136 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12136, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12137 member12137
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12137 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12137, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12138 member12138
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12138 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12138, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12139 member12139
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12139 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12139, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12140 member12140
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12140 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12140, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12141 member12141
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12141 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12141, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12142 member12142
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12142 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12142, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12143 member12143
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12143 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12143, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12144 member12144
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12144 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12144, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12145 member12145
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12145 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12145, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12154 member12154
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12154 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12154, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12167 member12167
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12167 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12167, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12168 member12168
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12168 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12168, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12169 member12169
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12169 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12169, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12170 member12170
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12170 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12170, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12171 member12171
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12171 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12171, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12172 member12172
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12172 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12172, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12173 member12173
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12173 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12173, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12174 member12174
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12174 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 65 row columns65 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12174, Expr.evalInteger, integerConstant, fieldModulus] using lifted

def intervals66 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 2130706432⟩
]
def columns66 (col : Nat) : Interval := intervals66[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds66 (tables : Tables) (row : Nat)
    (inside : row < (tables 66).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns66 col).Contains ((readCell tables 66 col row).val : Int) := by
  intro col
  have bound := (readCell tables 66 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 66 col row).val := by omega
  by_cases small : col < 16
  · have bounds := bounds66 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 66 0 row).val ∧
        ((readCell tables 66 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 66 1 row).val ∧
        ((readCell tables 66 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 66 2 row).val ∧
        ((readCell tables 66 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 66 3 row).val ∧
        ((readCell tables 66 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 66 4 row).val ∧
        ((readCell tables 66 4 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 66 5 row).val ∧
        ((readCell tables 66 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 66 6 row).val ∧
        ((readCell tables 66 6 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 66 7 row).val ∧
        ((readCell tables 66 7 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 66 8 row).val ∧
        ((readCell tables 66 8 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 66 9 row).val ∧
        ((readCell tables 66 9 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b9; omega
    · change (0 : Int) ≤ (readCell tables 66 10 row).val ∧
        ((readCell tables 66 10 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b10; omega
    · change (0 : Int) ≤ (readCell tables 66 11 row).val ∧
        ((readCell tables 66 11 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b11; omega
    · change (0 : Int) ≤ (readCell tables 66 12 row).val ∧
        ((readCell tables 66 12 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b12; omega
    · change (0 : Int) ≤ (readCell tables 66 13 row).val ∧
        ((readCell tables 66 13 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b13; omega
    · change (0 : Int) ≤ (readCell tables 66 14 row).val ∧
        ((readCell tables 66 14 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b14; omega
    · change (0 : Int) ≤ (readCell tables 66 15 row).val ∧
        ((readCell tables 66 15 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
  · have missing : intervals66[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals66] using Nat.le_of_not_gt small
    simp only [columns66, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations66 (v : Nat → Int) : Prop where
  h12176 : (((1 : Int) * (v 14)) * ((v 10) - (v 1))) = 0
  h12177 : (((1 : Int) * (v 14)) * ((((0 : Int) + (v 9)) + (((1 : Int) * (32768 : Int)) * (v 4))) - (v 0))) = 0
  h12179 : (((1 : Int) * (v 14)) * ((((((0 : Int) + (((1 : Int) * (((0 : Int) + (v 0)) + (v 1))) * ((1 : Int) - (v 11)))) + (((1 : Int) * (v 3)) * ((1 : Int) - (v 11)))) + (((1 : Int) * (v 2)) * ((1 : Int) - (v 11)))) + ((((1 : Int) * (v 11)) * ((65535 : Int) - (v 6))) * ((1 : Int) - (v 4)))) + ((((1 : Int) * (v 11)) * ((65535 : Int) - (v 5))) * ((1 : Int) - (v 4))))) = 0
  h12180 : (((((1 : Int) * (v 14)) * (v 11)) * (((((0 : Int) + (v 1)) + (-1 : Int)) + (((1 : Int) * (65536 : Int)) * (v 12))) - (v 8))) * ((1 : Int) - (v 4))) = 0
  h12181 : (((((1 : Int) * (v 14)) * (v 11)) * (((v 7) - (v 0)) - (((1 : Int) * (-1 : Int)) * (v 12)))) * ((1 : Int) - (v 4))) = 0
  h12182 : (((((1 : Int) * (v 14)) * (v 11)) * ((((v 3) - (v 6)) - (((1 : Int) * (-1 : Int)) * (v 8))) - (((1 : Int) * (65536 : Int)) * (v 13)))) * ((1 : Int) - (v 4))) = 0
  h12183 : (((((1 : Int) * (v 14)) * (v 11)) * ((((v 2) - (v 5)) - (((1 : Int) * (-1 : Int)) * (v 7))) - (((1 : Int) * (-1 : Int)) * (v 13)))) * ((1 : Int) - (v 4))) = 0
  h12184 : (((1 : Int) * (v 14)) * (((0 : Int) + ((((1 : Int) * (v 4)) * (v 11)) * ((65535 : Int) - (v 8)))) + ((((1 : Int) * (v 4)) * (v 11)) * ((65535 : Int) - (v 7))))) = 0
  h12185 : (((((1 : Int) * (v 14)) * (v 4)) * (v 11)) * ((((v 6) - (v 8)) - (((1 : Int) * (-1 : Int)) * (v 1))) - (((1 : Int) * (65536 : Int)) * (v 12)))) = 0
  h12186 : (((((1 : Int) * (v 14)) * (v 4)) * (v 11)) * ((((v 5) - (v 7)) - (((1 : Int) * (-1 : Int)) * (v 0))) - (((1 : Int) * (-1 : Int)) * (v 12)))) = 0
  h12187 : (((((1 : Int) * (v 14)) * (v 4)) * (v 11)) * (((((0 : Int) + (v 3)) + (((1 : Int) * (65536 : Int)) * (v 13))) - (v 6)) - (1 : Int))) = 0
  h12188 : (((((1 : Int) * (v 14)) * (v 4)) * (v 11)) * (((v 2) - (v 5)) - (v 13))) = 0
  h12193 : ((((1 : Int) * (v 4)) * (v 4)) - (v 4)) = 0
  h12200 : ((((1 : Int) * (v 11)) * (v 11)) - (v 11)) = 0
  h12201 : ((((1 : Int) * (v 12)) * (v 12)) - (v 12)) = 0
  h12202 : ((((1 : Int) * (v 13)) * (v 13)) - (v 13)) = 0
  h12203 : ((((1 : Int) * (v 14)) * (v 14)) - (v 14)) = 0

theorem integer_equations66 (tables : Tables) (row : Nat)
    (inside : row < (tables 66).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations66 (fun col => ((readCell tables 66 col row).val : Int)) := by
  have bounded := column_bounds66 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c12176 member12176
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12176 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12176, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12177 member12177
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12177 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12177, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12179 member12179
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12179 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12179, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12180 member12180
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12180 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12180, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12181 member12181
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12181 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12181, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12182 member12182
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12182 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12182, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12183 member12183
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12183 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12183, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12184 member12184
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12184 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12184, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12185 member12185
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12185 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12185, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12186 member12186
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12186 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12186, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12187 member12187
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12187 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12187, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12188 member12188
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12188 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12188, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12193 member12193
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12193 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12193, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12200 member12200
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12200 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12200, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12201 member12201
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12201 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12201, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12202 member12202
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12202 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12202, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c12203 member12203
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c12203 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 66 row columns66 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c12203, Expr.evalInteger, integerConstant, fieldModulus] using lifted

end DivRemFV.Generated
