module
public import CaptureClosure.Proof.PortModel
public import CaptureClosure.Proof.PortLayouts
public import CaptureClosure.Proof.ColumnIDs
public import CaptureClosure.Proof.UIntRef

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
local notation "BusPort" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port
open github_com.LFDT_Lineth.zkc.pkg.trace

def busPortModel [FfiSyntax] (source : BusPort) (columns : List w64) : DivRemFV.CaptureSyntax.Port :=
  ⟨source.Module'.toNat,some source.Selector'.index'.toNat,columns.map BitVec.toNat⟩

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Vector.TypeAssumptions] [ColumnId.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.TypeAssumptions]
variable [FuncUnfold busVector [] busVector.impl]
variable [FuncUnfold uintRef [] uintRef.impl]
variable [FuncUnfold exportColumnIDs [] exportColumnIDs.impl]

theorem capture_bus (source : BusPort) (columns : List w64) (dq : DFrac)
    (selectorValid : source.Selector'.index' ≠ W64 (2^64-1))
    (columnsValid : ∀ index ∈ columns, index ≠ W64 (2^64-1)) :
    {{ (source.Registers' ↦*{dq} registerIds columns : IProp GF) }}
      (App (Val (@! busVector)) (Val #source))
    {{ (result : Vector), RET #result;
      PortValue (busPortModel source columns) result (DFrac.own 1) ∗
        source.Registers' ↦*{dq} registerIds columns }} := by
  wp_start as Hsource
  wp_auto
  wp_apply (capture_uint_ref source.Selector'.index' selectorValid)
    with %selector Hselector
  all_goals try itrivial
  wp_apply (capture_column_ids source.Registers' columns dq columnsValid)
    $$ [Hsource] with %out ⟨Hcolumns,Hcap,Hsource⟩
  · iframe Hsource
  ihave ⟨Hselector,%Hnonnull⟩ := typedPointsto_not_null_dup selector source.Selector'.index'
    (DFrac.own 1) $$ Hselector
  iapply HΦ
  iframe Hsource
  isimp only [PortValue]
  iexists (some source.Selector'.index'),columns
  isplitl []
  · ipureintro; rfl
  isimp only [OptionalWord]
  iframe Hselector Hcolumns
  ipureintro; exact Hnonnull

#print axioms capture_bus
end
end divremfv.internal.airdata.SourceCapture
end Perennial
