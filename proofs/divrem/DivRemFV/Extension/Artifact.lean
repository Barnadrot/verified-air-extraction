import DivRemFV.RowSemantics

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV.Extension

def c12204 : Constraint := .vanishing 67 none (.mul (.mul (.constant 1) (.column 9 (0))) (.sub (.column 8 (0)) (.column 1 (0))))
def c12205 : Constraint := .vanishing 67 none (.mul (.mul (.constant 1) (.column 9 (0))) (.sub (.add (.add (.constant 0) (.column 7 (0))) (.mul (.mul (.constant 1) (.constant ⟨32768, by decide⟩)) (.column 6 (0)))) (.column 0 (0))))
def c12206 : Constraint := .vanishing 67 none (.mul (.mul (.mul (.constant 1) (.column 9 (0))) (.sub (.column 5 (0)) (.column 1 (0)))) (.column 6 (0)))
def c12207 : Constraint := .vanishing 67 none (.mul (.mul (.mul (.constant 1) (.column 9 (0))) (.sub (.column 4 (0)) (.column 0 (0)))) (.column 6 (0)))
def c12208 : Constraint := .vanishing 67 none (.mul (.mul (.constant 1) (.column 9 (0))) (.add (.add (.constant 0) (.mul (.mul (.constant 1) (.sub (.constant ⟨65535, by decide⟩) (.column 3 (0)))) (.column 6 (0)))) (.mul (.mul (.constant 1) (.sub (.constant ⟨65535, by decide⟩) (.column 2 (0)))) (.column 6 (0)))))
def c12209 : Constraint := .vanishing 67 none (.mul (.mul (.mul (.constant 1) (.column 9 (0))) (.sub (.constant ⟨1, by decide⟩) (.column 6 (0)))) (.sub (.column 5 (0)) (.column 1 (0))))
def c12210 : Constraint := .vanishing 67 none (.mul (.mul (.mul (.constant 1) (.column 9 (0))) (.sub (.constant ⟨1, by decide⟩) (.column 6 (0)))) (.sub (.column 4 (0)) (.column 0 (0))))
def c12211 : Constraint := .vanishing 67 none (.mul (.mul (.constant 1) (.column 9 (0))) (.add (.add (.constant 0) (.mul (.mul (.constant 1) (.sub (.constant ⟨1, by decide⟩) (.column 6 (0)))) (.column 3 (0)))) (.mul (.mul (.constant 1) (.sub (.constant ⟨1, by decide⟩) (.column 6 (0)))) (.column 2 (0)))))
def c12212 : Constraint := .lookup [⟨67, none, #[0]⟩] [⟨98, none, #[0]⟩]
def c12213 : Constraint := .lookup [⟨67, none, #[1]⟩] [⟨98, none, #[0]⟩]
def c12214 : Constraint := .lookup [⟨67, none, #[2]⟩] [⟨98, none, #[0]⟩]
def c12215 : Constraint := .lookup [⟨67, none, #[3]⟩] [⟨98, none, #[0]⟩]
def c12216 : Constraint := .lookup [⟨67, none, #[4]⟩] [⟨98, none, #[0]⟩]
def c12217 : Constraint := .lookup [⟨67, none, #[5]⟩] [⟨98, none, #[0]⟩]
def c12218 : Constraint := .vanishing 67 none (.sub (.mul (.mul (.constant 1) (.column 6 (0))) (.column 6 (0))) (.column 6 (0)))
def c12219 : Constraint := .lookup [⟨67, none, #[7]⟩] [⟨97, none, #[0]⟩]
def c12220 : Constraint := .lookup [⟨67, none, #[8]⟩] [⟨98, none, #[0]⟩]
def c12221 : Constraint := .vanishing 67 none (.sub (.mul (.mul (.constant 1) (.column 9 (0))) (.column 9 (0))) (.column 9 (0)))

def constraints : List Constraint := [
  c12204,
  c12205,
  c12206,
  c12207,
  c12208,
  c12209,
  c12210,
  c12211,
  c12212,
  c12213,
  c12214,
  c12215,
  c12216,
  c12217,
  c12218,
  c12219,
  c12220,
  c12221
]

theorem member12204 : c12204 ∈ constraints := List.getElem_mem (l := constraints) (n := 0) (by decide)
theorem member12205 : c12205 ∈ constraints := List.getElem_mem (l := constraints) (n := 1) (by decide)
theorem member12206 : c12206 ∈ constraints := List.getElem_mem (l := constraints) (n := 2) (by decide)
theorem member12207 : c12207 ∈ constraints := List.getElem_mem (l := constraints) (n := 3) (by decide)
theorem member12208 : c12208 ∈ constraints := List.getElem_mem (l := constraints) (n := 4) (by decide)
theorem member12209 : c12209 ∈ constraints := List.getElem_mem (l := constraints) (n := 5) (by decide)
theorem member12210 : c12210 ∈ constraints := List.getElem_mem (l := constraints) (n := 6) (by decide)
theorem member12211 : c12211 ∈ constraints := List.getElem_mem (l := constraints) (n := 7) (by decide)
theorem member12212 : c12212 ∈ constraints := List.getElem_mem (l := constraints) (n := 8) (by decide)
theorem member12213 : c12213 ∈ constraints := List.getElem_mem (l := constraints) (n := 9) (by decide)
theorem member12214 : c12214 ∈ constraints := List.getElem_mem (l := constraints) (n := 10) (by decide)
theorem member12215 : c12215 ∈ constraints := List.getElem_mem (l := constraints) (n := 11) (by decide)
theorem member12216 : c12216 ∈ constraints := List.getElem_mem (l := constraints) (n := 12) (by decide)
theorem member12217 : c12217 ∈ constraints := List.getElem_mem (l := constraints) (n := 13) (by decide)
theorem member12218 : c12218 ∈ constraints := List.getElem_mem (l := constraints) (n := 14) (by decide)
theorem member12219 : c12219 ∈ constraints := List.getElem_mem (l := constraints) (n := 15) (by decide)
theorem member12220 : c12220 ∈ constraints := List.getElem_mem (l := constraints) (n := 16) (by decide)
theorem member12221 : c12221 ∈ constraints := List.getElem_mem (l := constraints) (n := 17) (by decide)
structure Equations67 (v : Nat → K) : Prop where
  h12204 : (((1 : K) * (v 9)) * ((v 8) - (v 1))) = 0
  h12205 : (((1 : K) * (v 9)) * ((((0 : K) + (v 7)) + (((1 : K) * (32768 : K)) * (v 6))) - (v 0))) = 0
  h12206 : ((((1 : K) * (v 9)) * ((v 5) - (v 1))) * (v 6)) = 0
  h12207 : ((((1 : K) * (v 9)) * ((v 4) - (v 0))) * (v 6)) = 0
  h12208 : (((1 : K) * (v 9)) * (((0 : K) + (((1 : K) * ((65535 : K) - (v 3))) * (v 6))) + (((1 : K) * ((65535 : K) - (v 2))) * (v 6)))) = 0
  h12209 : ((((1 : K) * (v 9)) * ((1 : K) - (v 6))) * ((v 5) - (v 1))) = 0
  h12210 : ((((1 : K) * (v 9)) * ((1 : K) - (v 6))) * ((v 4) - (v 0))) = 0
  h12211 : (((1 : K) * (v 9)) * (((0 : K) + (((1 : K) * ((1 : K) - (v 6))) * (v 3))) + (((1 : K) * ((1 : K) - (v 6))) * (v 2)))) = 0
  h12218 : ((((1 : K) * (v 6)) * (v 6)) - (v 6)) = 0
  h12221 : ((((1 : K) * (v 9)) * (v 9)) - (v 9)) = 0

theorem equations67 (tables : Tables) (row : Nat)
    (inside : row < (tables 67).size) (accepted : ConstraintsHold tables constraints) :
    Equations67 (fun col => ((readCell tables 67 col row).val : K)) := by
  constructor
  · have h := accepted c12204 member12204
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast
  · have h := accepted c12205 member12205
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast
  · have h := accepted c12206 member12206
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast
  · have h := accepted c12207 member12207
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast
  · have h := accepted c12208 member12208
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast
  · have h := accepted c12209 member12209
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast
  · have h := accepted c12210 member12210
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast
  · have h := accepted c12211 member12211
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast
  · have h := accepted c12218 member12218
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast
  · have h := accepted c12221 member12221
    have value := h row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside)
    have cast := congrArg (fun n : Nat => (n : K)) value
    simpa only [Expr.eval_field_bridge, Expr.evalField, Nat.cast_zero, Int.add_zero] using cast

structure Bounds67 (v : Nat → Nat) : Prop where
  b0 : v 0 < 65536
  b1 : v 1 < 65536
  b2 : v 2 < 65536
  b3 : v 3 < 65536
  b4 : v 4 < 65536
  b5 : v 5 < 65536
  b6 : v 6 < 2
  b7 : v 7 < 32768
  b8 : v 8 < 65536
  b9 : v 9 < 2

theorem bounds67 (tables : Tables) (row : Nat)
    (inside : row < (tables 67).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    Bounds67 (fun col => (readCell tables 67 col row).val) := by
  have equations := equations67 tables row inside accepted
  constructor
  · exact lookup_range_bound tables 67 0 98 16 row inside
      (by simpa only [c12212] using accepted c12212 member12212) (ranges 98 16 (by decide))
  · exact lookup_range_bound tables 67 1 98 16 row inside
      (by simpa only [c12213] using accepted c12213 member12213) (ranges 98 16 (by decide))
  · exact lookup_range_bound tables 67 2 98 16 row inside
      (by simpa only [c12214] using accepted c12214 member12214) (ranges 98 16 (by decide))
  · exact lookup_range_bound tables 67 3 98 16 row inside
      (by simpa only [c12215] using accepted c12215 member12215) (ranges 98 16 (by decide))
  · exact lookup_range_bound tables 67 4 98 16 row inside
      (by simpa only [c12216] using accepted c12216 member12216) (ranges 98 16 (by decide))
  · exact lookup_range_bound tables 67 5 98 16 row inside
      (by simpa only [c12217] using accepted c12217 member12217) (ranges 98 16 (by decide))
  · exact scalar_boolean_bound (readCell tables 67 6 row) (by simpa only [zero_add, one_mul] using equations.h12218)
  · exact lookup_range_bound tables 67 7 97 15 row inside
      (by simpa only [c12219] using accepted c12219 member12219) (ranges 97 15 (by decide))
  · exact lookup_range_bound tables 67 8 98 16 row inside
      (by simpa only [c12220] using accepted c12220 member12220) (ranges 98 16 (by decide))
  · exact scalar_boolean_bound (readCell tables 67 9 row) (by simpa only [zero_add, one_mul] using equations.h12221)

end DivRemFV.Extension
