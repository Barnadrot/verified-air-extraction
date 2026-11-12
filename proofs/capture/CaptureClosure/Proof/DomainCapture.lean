module
public import CaptureClosure.Proof.OptionReads
public import CaptureClosure.Proof.ColumnWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
local notation "Option64" => github_com.LFDT_Lineth.zkc.pkg.util.Option w64

def domainValue [FfiSyntax] (source : Option64) : Option w64 :=
  if source.some' then some source.value' else none

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [FuncUnfold exportDomain [] exportDomain.impl]

theorem capture_domain (source : Option64) :
    {{ (True : IProp GF) }}
      (App (Val (@! exportDomain)) (Val #source))
    {{ (result : Loc), RET #result; OptionalWord result (domainValue source) (DFrac.own 1) }} := by
  wp_start
  wp_auto
  wp_apply (github_com.LFDT_Lineth.zkc.pkg.util.Option.hasValue_correct go.int source)
  all_goals try itrivial
  cases present : source.some' with
  | false =>
    try wp_auto
    iapply HΦ
    simp only [domainValue,present,Bool.false_eq_true,ite_false,OptionalWord]
    ipureintro; trivial
  | true =>
    try wp_auto
    wp_apply (github_com.LFDT_Lineth.zkc.pkg.util.Option.unwrap_correct go.int source present)
    all_goals try itrivial
    try wp_auto
    ihave ⟨value,%Hnonnull⟩ := typedPointsto_not_null_dup value_ptr source.value' (DFrac.own 1) $$ value
    iapply HΦ
    simp only [domainValue,present,ite_true,OptionalWord]
    iframe value
    ipureintro; exact Hnonnull

#print axioms capture_domain
end
end divremfv.internal.airdata.SourceCapture
end Perennial
