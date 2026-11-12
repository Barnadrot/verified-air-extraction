module
public import CaptureClosure.Proof.RecursiveWire

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
variable [FuncUnfold EncodeTermWire [] EncodeTermWire.impl]
variable [FuncUnfold appendTermWire [] appendTermWire.impl]
variable [FuncUnfold appendArgsWire [] appendArgsWire.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

theorem encode_term (model : ModelTerm) (value : Term) :
    {{ (OutputTerm (GF := GF) model value : IProp GF) }}
      (App (Val (@! EncodeTermWire)) (Val #value))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* wireBytes model.words ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OutputTerm model value }} := by
  wp_start as Hmodel
  wp_auto
  wp_apply (wire_term model slice.nil [] value) $$ [Hmodel]
    with %result ⟨Hout,Hcap,Hmodel⟩
  · isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    iexact Hmodel
  iapply HΦ
  isimp only [List.nil_append] at Hout
  iframe Hout Hcap Hmodel

#print axioms encode_term
end
end divremfv.internal.airdata.SourceCapture
end Perennial
