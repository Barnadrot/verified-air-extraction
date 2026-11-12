module
public import CaptureClosure.Proof.WordWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

def boolBytes (value : Bool) : List w8 :=
  u64Le (if value then W64 1 else W64 0) ++ u64Le (W64 0)

section bool_writer
variable [FuncUnfold appendWireBool [] appendWireBool.impl]

theorem append_bool (out : GoSlice) (prior : List w8) (value : Bool) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! appendWireBool)) (Val #out)) (Val #value))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ boolBytes value) ∗ ownSliceCap w8 result (DFrac.own 1) }} := by
  wp_start as ⟨Hout,Hcap⟩
  cases value <;> wp_auto
  all_goals
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    iapply HΦ
    simp only [boolBytes,Bool.false_eq_true,ite_false,ite_true]
    rw [← List.append_assoc]
    iframe Hout Hcap

end bool_writer

variable [FuncUnfold appendWireOption [] appendWireOption.impl]

theorem append_option_none (out : GoSlice) (prior : List w8) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! appendWireOption)) (Val #out)) (Val #Loc.null))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ u64Le (W64 0) ++ u64Le (W64 0)) ∗ ownSliceCap w8 result (DFrac.own 1) }} := by
  wp_start as ⟨Hout,Hcap⟩
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  iapply HΦ
  iframe Hout Hcap

theorem append_option_some (out : GoSlice) (prior : List w8) (p : Loc) (value : w64)
    (nonnull : p ≠ null) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ p ↦□ value : IProp GF) }}
      (App (App (Val (@! appendWireOption)) (Val #out)) (Val #p))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ u64Le (W64 1) ++ u64Le value) ∗ ownSliceCap w8 result (DFrac.own 1) }} := by
  wp_start as ⟨Hout,Hcap,#Hvalue⟩
  wp_auto
  rw [show decide (p = null) = false from decide_eq_false nonnull]
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  iapply HΦ
  iframe Hout Hcap

#print axioms append_bool
#print axioms append_option_none
#print axioms append_option_some

theorem append_option_some_frac (out : GoSlice) (prior : List w8) (p : Loc) (value : w64)
    (dq : DFrac) (nonnull : p ≠ null) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ p ↦{dq} value : IProp GF) }}
      (App (App (Val (@! appendWireOption)) (Val #out)) (Val #p))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ u64Le (W64 1) ++ u64Le value) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ p ↦{dq} value }} := by
  wp_start as ⟨Hout,Hcap,Hvalue⟩
  wp_auto
  rw [show decide (p = null) = false from decide_eq_false nonnull]
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  iapply HΦ
  iframe Hout Hcap Hvalue

#print axioms append_option_some_frac
end
end divremfv.internal.airdata.SourceCapture
end Perennial
