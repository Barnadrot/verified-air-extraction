import DivRemFV.RowSemantics

namespace DivRemFV.NativeImport

inductive Op where
  | add | sub | mul

def Op.expr : Op → Expr → Expr → Expr
  | .add => Expr.add
  | .sub => Expr.sub
  | .mul => Expr.mul

def Op.field : Op → K → K → K
  | .add => (·+·)
  | .sub => (·-·)
  | .mul => (·*·)

mutual
  inductive Term where
    | constant (value : Scalar)
    | column (id : Nat) (shift : Int)
    | sum (args : Args)
    | difference (first : Term) (rest : Args)
    | product (args : Args)
  inductive Args where
    | nil
    | cons (head : Term) (tail : Args)
end

mutual
  def Term.translate : Term → Expr
    | .constant value => .constant value
    | .column id shift => .column id shift
    | .sum args => args.translateFold .add (.constant 0)
    | .difference first rest => rest.translateFold .sub first.translate
    | .product args => args.translateFold .mul (.constant 1)
  def Args.translateFold (op : Op) (acc : Expr) : Args → Expr
    | .nil => acc
    | .cons head tail => tail.translateFold op (op.expr acc head.translate)
end

mutual
  def Term.eval (tables : Tables) (mid : Nat) (row : Int) : Term → K
    | .constant value => (value.val : K)
    | .column id shift => ((readCell tables mid id (row+shift)).val : K)
    | .sum args => args.evalFold tables mid row .add 0
    | .difference first rest => rest.evalFold tables mid row .sub (first.eval tables mid row)
    | .product args => args.evalFold tables mid row .mul 1
  def Args.evalFold (tables : Tables) (mid : Nat) (row : Int) (op : Op) (acc : K) : Args → K
    | .nil => acc
    | .cons head tail => tail.evalFold tables mid row op (op.field acc (head.eval tables mid row))
end

theorem Op.eval_expr (tables : Tables) (mid : Nat) (row : Int) (op : Op) (a b : Expr) :
    (op.expr a b).evalField tables mid row = op.field (a.evalField tables mid row) (b.evalField tables mid row) := by
  cases op <;> rfl

mutual
  theorem Term.translate_eval (tables : Tables) (mid : Nat) (row : Int) (term : Term) :
      term.translate.evalField tables mid row = term.eval tables mid row := by
    cases term with
    | constant value => rfl
    | column id shift => rfl
    | sum args => exact Args.translateFold_eval tables mid row .add (.constant 0) args
    | difference first rest =>
      simpa only [Term.translate_eval tables mid row first] using
        Args.translateFold_eval tables mid row .sub first.translate rest
    | product args => exact Args.translateFold_eval tables mid row .mul (.constant 1) args
  theorem Args.translateFold_eval (tables : Tables) (mid : Nat) (row : Int) (op : Op) (acc : Expr) (args : Args) :
      (args.translateFold op acc).evalField tables mid row = args.evalFold tables mid row op (acc.evalField tables mid row) := by
    cases args with
    | nil => rfl
    | cons head tail =>
      simpa only [Op.eval_expr,Term.translate_eval tables mid row head] using
        Args.translateFold_eval tables mid row op (op.expr acc head.translate) tail
end

mutual
  def Term.bounds : Term → Nat × Nat
    | .constant _ => (0,0)
    | .column _ shift => ((-shift).toNat,shift.toNat)
    | .sum args | .product args => args.boundsFold (0,0)
    | .difference first rest => rest.boundsFold first.bounds
  def Args.boundsFold (acc : Nat × Nat) : Args → Nat × Nat
    | .nil => acc
    | .cons head tail => tail.boundsFold (max acc.1 head.bounds.1,max acc.2 head.bounds.2)
end

mutual
  theorem Term.translate_bounds (term : Term) : term.translate.bounds = term.bounds := by
    cases term with
    | constant value => rfl
    | column id shift => rfl
    | sum args => exact Args.translateFold_bounds .add (.constant 0) args
    | difference first rest =>
      simpa only [Term.translate_bounds first] using Args.translateFold_bounds .sub first.translate rest
    | product args => exact Args.translateFold_bounds .mul (.constant 1) args
  theorem Args.translateFold_bounds (op : Op) (acc : Expr) (args : Args) :
      (args.translateFold op acc).bounds = args.boundsFold acc.bounds := by
    cases args with
    | nil => rfl
    | cons head tail =>
      have bounds : (op.expr acc head.translate).bounds =
          (max acc.bounds.1 head.bounds.1,max acc.bounds.2 head.bounds.2) := by
        cases op <;> simp only [Op.expr,Expr.bounds,Term.translate_bounds head]
      simpa only [bounds] using Args.translateFold_bounds op (op.expr acc head.translate) tail
end

theorem Term.translate_zero (tables : Tables) (mid : Nat) (row : Int) (term : Term) :
    term.translate.eval tables mid row = 0 ↔ term.eval tables mid row = 0 := by
  constructor
  · intro zero
    rw [← Term.translate_eval,← Expr.eval_field_bridge,zero]
    rfl
  · intro zero
    have cast : (term.translate.eval tables mid row : K) = 0 := by
      rw [Expr.eval_field_bridge,Term.translate_eval,zero]
    exact lift_field_equality _ 0 (Expr.eval_canonical tables mid row term.translate) (by decide) cast

inductive RawConstraint where
  | vanishing (owner : Nat) (domain : Option Int) (term : Term)
  | range (owner column bits : Nat)
  | lookup (sources targets : List Port)
  | bus (sources targets : List Port)

def RawConstraint.translate : RawConstraint → Constraint
  | .vanishing owner domain term => .vanishing owner domain term.translate
  | .range owner column bits => .range owner column bits
  | .lookup sources targets => .lookup sources targets
  | .bus sources targets => .bus sources targets

def RawConstraint.Holds (tables : Tables) : RawConstraint → Prop
  | .vanishing mid none term =>
    ∀ row : Nat,term.bounds.1 ≤ row → row+term.bounds.2 < (tables mid).size → term.eval tables mid row = 0
  | .vanishing mid (some domain) term =>
    let row := if domain < 0 then (tables mid).size+domain else domain
    term.eval tables mid row = 0
  | .range mid col bits => ∀ row ∈ (tables mid).toList,(row[col]?.getD 0).val < 2^bits
  | .lookup sources targets => ∀ message ∈ messages tables sources,message ∈ messages tables targets
  | .bus sources targets => (messages tables sources).Perm (messages tables targets)

theorem RawConstraint.translate_holds (tables : Tables) (constraint : RawConstraint) :
    constraint.translate.Holds tables ↔ constraint.Holds tables := by
  cases constraint with
  | vanishing owner domain term =>
    cases domain with
    | none =>
      simp only [RawConstraint.translate,Constraint.Holds,RawConstraint.Holds,Term.translate_bounds,Term.translate_zero]
    | some domain => exact Term.translate_zero tables owner _ term
  | range owner col bits => rfl
  | lookup sources targets => rfl
  | bus sources targets => rfl

def RawConstraintsHold (tables : Tables) (constraints : List RawConstraint) : Prop :=
  ∀ constraint ∈ constraints,constraint.Holds tables

theorem translate_constraints_holds (tables : Tables) (constraints : List RawConstraint) :
    ConstraintsHold tables (constraints.map RawConstraint.translate) ↔ RawConstraintsHold tables constraints := by
  simp only [ConstraintsHold,RawConstraintsHold,List.mem_map,forall_exists_index,and_imp]
  constructor
  · intro accepted constraint member
    exact (RawConstraint.translate_holds tables constraint).1 (accepted _ constraint member rfl)
  · intro accepted translated constraint member equal
    subst translated
    exact (RawConstraint.translate_holds tables constraint).2 (accepted constraint member)

theorem project_indices_holds (tables : Tables) (all : Array RawConstraint) (indices : List Nat)
    (bounded : ∀ index ∈ indices,index < all.size)
    (accepted : RawConstraintsHold tables all.toList) :
    RawConstraintsHold tables (indices.map fun index => all[index]?.getD (.lookup [] [])) := by
  intro constraint member
  obtain ⟨index,present,rfl⟩ := List.mem_map.mp member
  have inside := bounded index present
  rw [Array.getElem?_eq_getElem inside,Option.getD_some]
  exact accepted all[index] (Array.getElem_mem_toList inside)

theorem indexed_project_holds (tables : Tables) (all : Nat → RawConstraint) (count : Nat) (indices : List Nat)
    (bounded : ∀ index ∈ indices,index < count)
    (accepted : ∀ index,index < count → (all index).Holds tables) :
    RawConstraintsHold tables (indices.map all) := by
  intro constraint member
  obtain ⟨index,present,rfl⟩ := List.mem_map.mp member
  exact accepted index (bounded index present)

end DivRemFV.NativeImport
