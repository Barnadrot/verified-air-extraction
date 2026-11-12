import DivRemFV.FieldLifting

namespace DivRemFV

structure Interval where
  lower : Int
  upper : Int
  deriving DecidableEq, Repr

def Interval.Contains (interval : Interval) (value : Int) : Prop :=
  interval.lower ≤ value ∧ value ≤ interval.upper

def Interval.add (a b : Interval) : Interval := ⟨a.lower + b.lower, a.upper + b.upper⟩
def Interval.sub (a b : Interval) : Interval := ⟨a.lower - b.upper, a.upper - b.lower⟩
def Interval.mul (a b : Interval) : Interval :=
  ⟨min (min (a.lower * b.lower) (a.lower * b.upper))
       (min (a.upper * b.lower) (a.upper * b.upper)),
   max (max (a.lower * b.lower) (a.lower * b.upper))
       (max (a.upper * b.lower) (a.upper * b.upper))⟩

private theorem mul_lower (x lo hi c : Int) (lower : lo ≤ x) (upper : x ≤ hi) :
    min (lo * c) (hi * c) ≤ x * c := by
  by_cases sign : 0 ≤ c
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right lower sign)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right upper (le_of_not_ge sign))

private theorem mul_upper (x lo hi c : Int) (lower : lo ≤ x) (upper : x ≤ hi) :
    x * c ≤ max (lo * c) (hi * c) := by
  by_cases sign : 0 ≤ c
  · exact (mul_le_mul_of_nonneg_right upper sign).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right lower (le_of_not_ge sign)).trans (le_max_left _ _)

theorem Interval.mul_correct {a b : Interval} {x y : Int}
    (ha : a.Contains x) (hb : b.Contains y) : (a.mul b).Contains (x * y) := by
  constructor
  · apply le_trans _ (show min (x * b.lower) (x * b.upper) ≤ x * y by
      simpa only [mul_comm] using mul_lower y b.lower b.upper x hb.1 hb.2)
    apply le_min
    · exact (min_le_min (min_le_left _ _) (min_le_left _ _)).trans
        (mul_lower x a.lower a.upper b.lower ha.1 ha.2)
    · exact (min_le_min (min_le_right _ _) (min_le_right _ _)).trans
        (mul_lower x a.lower a.upper b.upper ha.1 ha.2)
  · apply le_trans (show x * y ≤ max (x * b.lower) (x * b.upper) by
      simpa only [mul_comm] using mul_upper y b.lower b.upper x hb.1 hb.2)
    apply max_le
    · exact (mul_upper x a.lower a.upper b.lower ha.1 ha.2).trans
        (max_le_max (le_max_left _ _) (le_max_left _ _))
    · exact (mul_upper x a.lower a.upper b.upper ha.1 ha.2).trans
        (max_le_max (le_max_right _ _) (le_max_right _ _))

theorem field_minus_one : (2130706432 : K) = -1 := by
  change ((fieldModulus - 1 : Nat) : K) = -1
  rw [Nat.cast_sub (by decide), ZMod.natCast_self, Nat.cast_one]
  exact zero_sub 1

def integerConstant (value : Scalar) : Int :=
  if value.val = fieldModulus - 1 then -1 else value.val

theorem integerConstant_cast (value : Scalar) :
    (integerConstant value : K) = (value.val : K) := by
  unfold integerConstant
  split
  · rename_i equal
    rw [equal]
    simpa only [Int.cast_neg, Int.cast_one] using field_minus_one.symm
  · exact Int.cast_natCast value.val

def Expr.evalInteger (values : Nat → Int → Int) (row : Int) : Expr → Int
  | .constant value => integerConstant value
  | .column col shift => values col (row + shift)
  | .add a b => a.evalInteger values row + b.evalInteger values row
  | .sub a b => a.evalInteger values row - b.evalInteger values row
  | .mul a b => a.evalInteger values row * b.evalInteger values row

def Expr.interval (columns : Nat → Interval) : Expr → Interval
  | .constant value => ⟨integerConstant value, integerConstant value⟩
  | .column col _ => columns col
  | .add a b => (a.interval columns).add (b.interval columns)
  | .sub a b => (a.interval columns).sub (b.interval columns)
  | .mul a b => (a.interval columns).mul (b.interval columns)

theorem Expr.interval_correct (expr : Expr) (values : Nat → Int → Int)
    (columns : Nat → Interval) (bounded : ∀ col row, (columns col).Contains (values col row))
    (row : Int) : (expr.interval columns).Contains (expr.evalInteger values row) := by
  induction expr with
  | constant value => exact ⟨le_refl _, le_refl _⟩
  | column col shift => exact bounded col (row + shift)
  | add a b ha hb => exact ⟨add_le_add ha.1 hb.1, add_le_add ha.2 hb.2⟩
  | sub a b ha hb => exact ⟨sub_le_sub ha.1 hb.2, sub_le_sub ha.2 hb.1⟩
  | mul a b ha hb => exact Interval.mul_correct ha hb

theorem Expr.integer_field_bridge (expr : Expr) (tables : Tables) (mid : Nat) (row : Int) :
    (expr.evalInteger (fun col offset => (readCell tables mid col offset).val) row : K) =
      expr.evalField tables mid row := by
  induction expr with
  | constant value => exact integerConstant_cast value
  | column col shift => exact Int.cast_natCast _
  | add a b ha hb => simpa only [Expr.evalInteger, Expr.evalField, Int.cast_add] using congrArg₂ (· + ·) ha hb
  | sub a b ha hb => simpa only [Expr.evalInteger, Expr.evalField, Int.cast_sub] using congrArg₂ (· - ·) ha hb
  | mul a b ha hb => simpa only [Expr.evalInteger, Expr.evalField, Int.cast_mul] using congrArg₂ (· * ·) ha hb

theorem Expr.lift_zero (expr : Expr) (tables : Tables) (mid : Nat) (row : Int)
    (columns : Nat → Interval)
    (bounded : ∀ col offset, (columns col).Contains ((readCell tables mid col offset).val : Int))
    (lower : -(fieldModulus : Int) < (expr.interval columns).lower)
    (upper : (expr.interval columns).upper < fieldModulus)
    (zero : expr.evalField tables mid row = 0) :
    expr.evalInteger (fun col offset => (readCell tables mid col offset).val) row = 0 := by
  have range := expr.interval_correct _ _ bounded row
  apply lift_integer_zero _ (lt_of_lt_of_le lower range.1) (lt_of_le_of_lt range.2 upper)
  simpa only [Expr.integer_field_bridge] using zero

def Expr.noShifts : Expr → Bool
  | .constant _ => true
  | .column _ shift => shift == 0
  | .add a b | .sub a b | .mul a b => a.noShifts && b.noShifts

theorem Expr.integer_row_bridge (expr : Expr) (tables : Tables) (mid : Nat) (row : Int)
    (unshifted : expr.noShifts = true) :
    (expr.evalInteger (fun col _ => (readCell tables mid col row).val) row : K) =
      expr.evalField tables mid row := by
  induction expr with
  | constant value => exact integerConstant_cast value
  | column col shift =>
    have zero : shift = 0 := by simpa [Expr.noShifts] using unshifted
    subst shift
    simp only [Expr.evalInteger, Expr.evalField, Int.add_zero, Int.cast_natCast]
  | add a b ha hb =>
    have parts : a.noShifts = true ∧ b.noShifts = true := by simpa [Expr.noShifts] using unshifted
    simpa only [Expr.evalInteger, Expr.evalField, Int.cast_add] using congrArg₂ (· + ·) (ha parts.1) (hb parts.2)
  | sub a b ha hb =>
    have parts : a.noShifts = true ∧ b.noShifts = true := by simpa [Expr.noShifts] using unshifted
    simpa only [Expr.evalInteger, Expr.evalField, Int.cast_sub] using congrArg₂ (· - ·) (ha parts.1) (hb parts.2)
  | mul a b ha hb =>
    have parts : a.noShifts = true ∧ b.noShifts = true := by simpa [Expr.noShifts] using unshifted
    simpa only [Expr.evalInteger, Expr.evalField, Int.cast_mul] using congrArg₂ (· * ·) (ha parts.1) (hb parts.2)

theorem Expr.lift_row_zero (expr : Expr) (tables : Tables) (mid : Nat) (row : Int)
    (columns : Nat → Interval)
    (bounded : ∀ col, (columns col).Contains ((readCell tables mid col row).val : Int))
    (unshifted : expr.noShifts = true)
    (lower : -(fieldModulus : Int) < (expr.interval columns).lower)
    (upper : (expr.interval columns).upper < fieldModulus)
    (zero : expr.evalField tables mid row = 0) :
    expr.evalInteger (fun col _ => (readCell tables mid col row).val) row = 0 := by
  have range := expr.interval_correct _ _ (fun col _ => bounded col) row
  apply lift_integer_zero _ (lt_of_lt_of_le lower range.1) (lt_of_le_of_lt range.2 upper)
  simpa only [Expr.integer_row_bridge _ _ _ _ unshifted] using zero

end DivRemFV

