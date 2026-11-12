module
public import CaptureClosure.Proof.ColumnId
public import CaptureClosure.Code.divremfv.internal.airdata

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.trace

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [ColumnId.TypeAssumptions]
variable [FuncUnfold uintRef [] uintRef.impl]

theorem capture_uint_ref (index : w64) (valid : index ≠ W64 (2^64-1)) :
    {{ (True : IProp GF) }}
      (App (Val (@! uintRef)) (Val #(ColumnId.mk index)))
    {{ (result : Loc), RET #result; result ↦ index }} := by
  wp_start as _
  wp_auto
  wp_apply (ColumnId.unwrap_correct index valid)
  all_goals try itrivial
  try wp_auto
  iapply HΦ
  iframe

#print axioms capture_uint_ref
end
end divremfv.internal.airdata.SourceCapture
end Perennial
