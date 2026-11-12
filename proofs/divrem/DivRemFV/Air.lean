import Std

namespace DivRemFV

def fieldModulus : Nat := 2130706433

instance : NeZero fieldModulus := ⟨by decide⟩

abbrev Scalar := Fin fieldModulus

inductive Expr where
  | constant (value : Scalar)
  | column (id : Nat) (shift : Int)
  | add (left right : Expr)
  | sub (left right : Expr)
  | mul (left right : Expr)
  deriving Repr, Inhabited, DecidableEq

abbrev Row := Array Scalar
abbrev Tables := Nat → Array Row

def readCell (tables : Tables) (mid col : Nat) (row : Int) : Scalar :=
  if row < 0 then 0 else
    ((tables mid)[row.toNat]?.getD #[])[col]?.getD 0

def Expr.eval (tables : Tables) (mid : Nat) (row : Int) : Expr → Nat
  | .constant n => n.val
  | .column col shift => (readCell tables mid col (row + shift)).val
  | .add a b => (a.eval tables mid row + b.eval tables mid row) % fieldModulus
  | .sub a b => (a.eval tables mid row + fieldModulus - b.eval tables mid row) % fieldModulus
  | .mul a b => (a.eval tables mid row * b.eval tables mid row) % fieldModulus

def Expr.bounds : Expr → Nat × Nat
  | .constant _ => (0, 0)
  | .column _ shift => ((-shift).toNat, shift.toNat)
  | .add a b | .sub a b | .mul a b =>
    (max a.bounds.1 b.bounds.1, max a.bounds.2 b.bounds.2)

theorem Expr.eval_canonical (tables : Tables) (mid : Nat) (row : Int) (expr : Expr) :
    expr.eval tables mid row < fieldModulus := by
  cases expr with
  | constant value => exact value.isLt
  | column col shift => exact (readCell tables mid col (row + shift)).isLt
  | add a b | sub a b | mul a b => exact Nat.mod_lt _ (by decide)

structure Port where
  moduleId : Nat
  selector : Option Nat
  columns : Array Nat
  deriving Repr, DecidableEq

def Port.messages (tables : Tables) (port : Port) : List (List Scalar) :=
  (tables port.moduleId).toList.filterMap fun row =>
    if port.selector.all (fun col => row[col]?.getD 0 != 0) then
      some (port.columns.toList.map fun col => row[col]?.getD 0)
    else none

inductive Constraint where
  | vanishing (owner : Nat) (domain : Option Int) (expr : Expr)
  | range (owner column bits : Nat)
  | lookup (sources targets : List Port)
  | bus (sources targets : List Port)
  deriving Repr, DecidableEq

def messages (tables : Tables) (ports : List Port) : List (List Scalar) :=
  ports.flatMap (Port.messages tables)

def Constraint.Holds (tables : Tables) : Constraint → Prop
  | .vanishing mid none expr =>
    ∀ row : Nat, expr.bounds.1 ≤ row → row + expr.bounds.2 < (tables mid).size →
      expr.eval tables mid row = 0
  | .vanishing mid (some domain) expr =>
    let row := if domain < 0 then (tables mid).size + domain else domain
    expr.eval tables mid row = 0
  | .range mid col bits =>
    ∀ row ∈ (tables mid).toList, (row[col]?.getD 0).val < 2 ^ bits
  | .lookup sources targets =>
    ∀ message ∈ messages tables sources, message ∈ messages tables targets
  | .bus sources targets =>
    (messages tables sources).Perm (messages tables targets)

def ConstraintsHold (tables : Tables) (constraints : List Constraint) : Prop :=
  ∀ c ∈ constraints, c.Holds tables

theorem constraints_subset (tables : Tables) (all selected : List Constraint)
    (subset : ∀ c ∈ selected, c ∈ all) (accepted : ConstraintsHold tables all) :
    ConstraintsHold tables selected :=
  fun c member => accepted c (subset c member)

end DivRemFV
