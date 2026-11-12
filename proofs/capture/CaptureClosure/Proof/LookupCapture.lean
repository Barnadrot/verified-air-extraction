module
public import CaptureClosure.Proof.BusCapture
public import CaptureClosure.Proof.OptionReads

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
local notation "LookupVector" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector
open github_com.LFDT_Lineth.zkc.pkg.trace

def lookupPortModel [FfiSyntax] (source : LookupVector) (columns : List w64) : DivRemFV.CaptureSyntax.Port :=
  ⟨source.Module'.toNat,
    if source.Selector'.some' then some source.Selector'.value'.index'.toNat else none,
    columns.map BitVec.toNat⟩

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Vector.TypeAssumptions] [ColumnId.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.TypeAssumptions]
variable [FuncUnfold lookupVector [] lookupVector.impl]
variable [FuncUnfold uintRef [] uintRef.impl]
variable [FuncUnfold exportColumnIDs [] exportColumnIDs.impl]

theorem capture_lookup (source : LookupVector) (columns : List w64) (dq : DFrac)
    (selectorValid : source.Selector'.some' = true → source.Selector'.value'.index' ≠ W64 (2^64-1))
    (columnsValid : ∀ index ∈ columns, index ≠ W64 (2^64-1)) :
    {{ (source.Registers' ↦*{dq} registerIds columns : IProp GF) }}
      (App (Val (@! lookupVector)) (Val #source))
    {{ (result : Vector), RET #result;
      PortValue (lookupPortModel source columns) result (DFrac.own 1) ∗
        source.Registers' ↦*{dq} registerIds columns }} := by
  wp_start as Hsource
  wp_auto
  wp_apply (capture_column_ids source.Registers' columns dq columnsValid)
    $$ [Hsource] with %out ⟨Hcolumns,Hcap,Hsource⟩
  · iframe Hsource
  wp_apply (github_com.LFDT_Lineth.zkc.pkg.util.Option.hasValue_correct
    ColumnId.ty source.Selector')
  all_goals try itrivial
  cases present : source.Selector'.some' with
  | false =>
    try wp_auto
    iapply HΦ
    iframe Hsource
    isimp only [PortValue]
    iexists none,columns
    isplitl []
    · ipureintro; simp [lookupPortModel,portablePort,present]
    isimp only [OptionalWord]
    iframe Hcolumns
  | true =>
    try wp_auto
    wp_apply (github_com.LFDT_Lineth.zkc.pkg.util.Option.unwrap_correct
      ColumnId.ty source.Selector' present)
    all_goals try itrivial
    wp_apply (capture_uint_ref source.Selector'.value'.index' (selectorValid present))
      with %selector Hselector
    all_goals try itrivial
    try wp_auto
    ihave ⟨Hselector,%Hnonnull⟩ := typedPointsto_not_null_dup selector source.Selector'.value'.index'
      (DFrac.own 1) $$ Hselector
    iapply HΦ
    iframe Hsource
    isimp only [PortValue]
    iexists (some source.Selector'.value'.index'),columns
    isplitl []
    · ipureintro; simp [lookupPortModel,portablePort,present]
    isimp only [OptionalWord]
    iframe Hselector Hcolumns
    ipureintro; exact Hnonnull

#print axioms capture_lookup
end
end divremfv.internal.airdata.SourceCapture
end Perennial
