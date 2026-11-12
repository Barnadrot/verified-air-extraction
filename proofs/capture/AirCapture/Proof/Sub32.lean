module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import AirCapture.Code.math.bits

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

private theorem borrow_one (x : w32) (bound : x.toNat < 2130706433) :
    ((~~~x &&& W32 2130706433) |||
      (~~~(x ^^^ W32 2130706433) &&& (x - W32 2130706433))) >>> 31 = W32 1 := by
  have hx : x.msb = false := by rw [BitVec.msb_eq_false_iff_two_mul_lt]; omega
  have hd : (x - W32 2130706433).msb = true := by
    rw [BitVec.msb_eq_true_iff_two_mul_ge]
    word
  have hm : (((~~~x &&& W32 2130706433) |||
      (~~~(x ^^^ W32 2130706433) &&& (x - W32 2130706433)))).msb = true := by
    simp only [BitVec.msb_or, BitVec.msb_and, BitVec.msb_not, BitVec.msb_xor,
      hx, hd, show (W32 2130706433).msb = false from rfl]
    rfl
  have hl := BitVec.msb_eq_true_iff_two_mul_ge.mp hm
  have hu := (((~~~x &&& W32 2130706433) |||
      (~~~(x ^^^ W32 2130706433) &&& (x - W32 2130706433)))).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change _ / 2147483648 = 1
  omega

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]

/-- Actual Go `Sub32`, specialized to the constant-capture call and its input bound. -/
theorem sub32_below_modulus (x : w32) (bound : x.toNat < 2130706433) :
    {{ (True : IProp GF) }}
      (App (App (App (Val (@! math.bits.Sub32)) (Val #x))
        (Val #(W32 2130706433))) (Val #(W32 0)))
    {{ RET (PairV #(x - W32 2130706433) #(W32 1)); True }} := by
  wp_start
  wp_auto
  rw [show x - W32 2130706433 - W32 0 = x - W32 2130706433 by word]
  rw [show ((~~~x &&& W32 2130706433) |||
    (~~~(x ^^^ W32 2130706433) &&& (x - W32 2130706433))) >>> W64 31 = W32 1
    from borrow_one x bound]
  wp_end

#print axioms sub32_below_modulus

theorem sub32_at_modulus :
    {{ (True : IProp GF) }}
      (App (App (App (Val (@! math.bits.Sub32)) (Val #(W32 2130706433)))
        (Val #(W32 2130706433))) (Val #(W32 0)))
    {{ RET (PairV #(W32 0) #(W32 0)); True }} := by
  wp_start
  wp_auto
  rw [show W32 2130706433 - W32 2130706433 - W32 0 = W32 0 by decide]
  rw [show ((~~~W32 2130706433 &&& W32 2130706433) |||
    (~~~(W32 2130706433 ^^^ W32 2130706433) &&& W32 0)) >>> W64 31 = W32 0 by decide]
  wp_end

#print axioms sub32_at_modulus
end
end Perennial
