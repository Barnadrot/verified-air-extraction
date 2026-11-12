module
public import CaptureClosure.Proof.ArgsWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Term.TypeAssumptions]
variable [FuncUnfold appendTermWire [] appendTermWire.impl]
variable [FuncUnfold appendArgsWire [] appendArgsWire.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

theorem append_sum (out : GoSlice) (prior : List w8) (sl : GoSlice)
    (models : ModelArgs) (values : List Term)
    (calls : ∀ model ∈ models.toList, ∀ (out : GoSlice) (prior : List w8) (value : Term),
      ⊢ iprop({{ out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OutputTerm (GF := GF) model value }}
        (App (App (Val (@! appendTermWire)) (Val #out)) (Val #value))
        {{ (result : GoSlice), RET (PairV #result #interface.nil);
          result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OutputTerm model value }})) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗
        sl ↦* values ∗ OutputArgs models values : IProp GF) }}
      (App (App (Val (@! appendTermWire)) (Val #out))
        (Val #(Term.mk go!"add" (W64 0) (W64 0) (W64 0) sl)))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* (prior ++ wireBytes (DivRemFV.CaptureSyntax.Term.sum models).words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗
      sl ↦* values ∗ OutputArgs models values }} := by
  wp_start as ⟨Hout,Hcap,Hsl,Hmodels⟩
  ihave Hlist := (output_args_list models values).1 $$ Hmodels
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply (append_args _ _ sl (DFrac.own 1) models.toList values calls)
    $$ [Hout Hcap Hsl Hlist] with %result ⟨Hout,Hcap,Hsl,Hlist⟩
  · iframe Hout Hcap Hsl Hlist
  iapply HΦ
  isimp only [List.append_assoc] at Hout
  simp only [DivRemFV.CaptureSyntax.Term.words,args_words,wireBytes_cons,List.append_assoc]
  iframe Hout Hcap Hsl
  iapply (output_args_list models values).2
  iexact Hlist

#print axioms append_sum

theorem append_product (out : GoSlice) (prior : List w8) (sl : GoSlice)
    (models : ModelArgs) (values : List Term)
    (calls : ∀ model ∈ models.toList, ∀ (out : GoSlice) (prior : List w8) (value : Term),
      ⊢ iprop({{ out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OutputTerm (GF := GF) model value }}
        (App (App (Val (@! appendTermWire)) (Val #out)) (Val #value))
        {{ (result : GoSlice), RET (PairV #result #interface.nil);
          result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OutputTerm model value }})) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗
        sl ↦* values ∗ OutputArgs models values : IProp GF) }}
      (App (App (Val (@! appendTermWire)) (Val #out))
        (Val #(Term.mk go!"mul" (W64 0) (W64 0) (W64 0) sl)))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* (prior ++ wireBytes (DivRemFV.CaptureSyntax.Term.product models).words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗
      sl ↦* values ∗ OutputArgs models values }} := by
  wp_start as ⟨Hout,Hcap,Hsl,Hmodels⟩
  ihave Hlist := (output_args_list models values).1 $$ Hmodels
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply (append_args _ _ sl (DFrac.own 1) models.toList values calls)
    $$ [Hout Hcap Hsl Hlist] with %result ⟨Hout,Hcap,Hsl,Hlist⟩
  · iframe Hout Hcap Hsl Hlist
  iapply HΦ
  isimp only [List.append_assoc] at Hout
  simp only [DivRemFV.CaptureSyntax.Term.words,args_words,wireBytes_cons,List.append_assoc]
  iframe Hout Hcap Hsl
  iapply (output_args_list models values).2
  iexact Hlist

#print axioms append_product
end
end divremfv.internal.airdata.SourceCapture
end Perennial
