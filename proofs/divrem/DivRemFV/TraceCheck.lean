import DivRemFV.Air
import Std.Data.HashSet.Lemmas

namespace DivRemFV.TraceCheck

abbrev Message := List Scalar

structure Index (entries : List Message) where
  values : Std.HashSet Message
  valid : ∀ message, values.contains message = true ↔ message ∈ entries

def index (entries : List Message) : Index entries :=
  ⟨Std.HashSet.ofList entries, by intro message; simp⟩

structure IndexedPort (tables : Tables) where
  port : Port
  entries : Index (port.messages tables)

def cached (tables : Tables) (cache : List (IndexedPort tables)) (port : Port) :
    Index (port.messages tables) :=
  match cache.find? (fun entry => entry.port == port) with
  | some entry => if same : entry.port = port then same ▸ entry.entries else index _
  | none => index _

def prepare (tables : Tables) (ports : List Port) : List (IndexedPort tables) :=
  ports.eraseDups.map fun port => ⟨port, index (port.messages tables)⟩

def constraint (tables : Tables) (cache : List (IndexedPort tables)) : Constraint → Bool
  | .vanishing mid none expr =>
    (List.range (tables mid).size).all fun row =>
      decide (expr.bounds.1 ≤ row ∧ row + expr.bounds.2 < (tables mid).size →
        expr.eval tables mid row = 0)
  | .vanishing mid (some domain) expr =>
    let row := if domain < 0 then (tables mid).size + domain else domain
    decide (expr.eval tables mid row = 0)
  | .range mid col bits =>
    (tables mid).toList.all fun row => decide ((row[col]?.getD 0).val < 2 ^ bits)
  | .lookup sources targets =>
    (messages tables sources).all fun message =>
      targets.any fun port => (cached tables cache port).values.contains message
  | .bus sources targets => decide ((messages tables sources).Perm (messages tables targets))

theorem constraint_iff (tables : Tables) (cache : List (IndexedPort tables)) (c : Constraint) :
    constraint tables cache c = true ↔ c.Holds tables := by
  cases c with
  | vanishing mid domain expr =>
    cases domain with
    | none =>
      simp only [constraint, Constraint.Holds, List.all_eq_true, List.mem_range, decide_eq_true_eq]
      constructor
      · intro checked row lower upper
        exact checked row (by omega) ⟨lower, upper⟩
      · intro holds row _ bounds
        exact holds row bounds.1 bounds.2
    | some domain => simp [constraint, Constraint.Holds]
  | range mid col bits =>
    simp only [constraint, Constraint.Holds, List.all_eq_true, decide_eq_true_eq]
  | lookup sources targets =>
    simp [constraint, Constraint.Holds, List.all_eq_true, List.any_eq_true,
      (cached tables cache _).valid, messages, List.mem_flatMap]
    constructor
    · intro holds message port member present
      exact holds port member message present
    · intro holds port member message present
      exact holds message port member present
  | bus sources targets => simp [constraint, Constraint.Holds]

def all (tables : Tables) (cache : List (IndexedPort tables)) (constraints : List Constraint) : Bool :=
  constraints.all (constraint tables cache)

theorem all_iff (tables : Tables) (cache : List (IndexedPort tables)) (constraints : List Constraint) :
    all tables cache constraints = true ↔ ConstraintsHold tables constraints := by
  simp [all, ConstraintsHold, List.all_eq_true, constraint_iff]

end DivRemFV.TraceCheck
