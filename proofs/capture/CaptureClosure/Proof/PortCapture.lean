module
public import CaptureClosure.Proof.LookupCapture
public import CaptureClosure.Proof.PortsWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
local notation "LookupVector" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector
local notation "BusPort" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port
open github_com.LFDT_Lineth.zkc.pkg.trace

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

def InputLookupPort (model : DivRemFV.CaptureSyntax.Port) (source : LookupVector) : IProp GF :=
  iprop(∃ columns : List w64,
    ⌜model = lookupPortModel source columns ∧
      (source.Selector'.some' = true → source.Selector'.value'.index' ≠ W64 (2^64-1)) ∧
      (∀ index ∈ columns, index ≠ W64 (2^64-1))⌝ ∗
    source.Registers' ↦*□ registerIds columns)

def InputBusPort (model : DivRemFV.CaptureSyntax.Port) (source : BusPort) : IProp GF :=
  iprop(∃ columns : List w64,
    ⌜model = busPortModel source columns ∧ source.Selector'.index' ≠ W64 (2^64-1) ∧
      (∀ index ∈ columns, index ≠ W64 (2^64-1))⌝ ∗
    source.Registers' ↦*□ registerIds columns)

instance (model : DivRemFV.CaptureSyntax.Port) (source : LookupVector) :
    Persistent (InputLookupPort (GF := GF) model source) := by unfold InputLookupPort; infer_instance
instance (model : DivRemFV.CaptureSyntax.Port) (source : BusPort) :
    Persistent (InputBusPort (GF := GF) model source) := by unfold InputBusPort; infer_instance

variable [Vector.TypeAssumptions] [ColumnId.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.TypeAssumptions]
variable [FuncUnfold lookupVector [] lookupVector.impl]
variable [FuncUnfold busVector [] busVector.impl]
variable [FuncUnfold uintRef [] uintRef.impl]
variable [FuncUnfold exportColumnIDs [] exportColumnIDs.impl]

theorem capture_lookup_model (model : DivRemFV.CaptureSyntax.Port) (source : LookupVector) :
    {{ (InputLookupPort model source : IProp GF) }}
      (App (Val (@! lookupVector)) (Val #source))
    {{ (result : Vector), RET #result; PortValue model result (DFrac.own 1) ∗ InputLookupPort model source }} := by
  iintro %Φ #Hmodel HΦ
  ihave #Hsaved := Hmodel
  isimp only [InputLookupPort] at Hmodel
  icases Hmodel with ⟨%columns,⟨%Heq,%Hselector,%Hcolumns⟩,Hsource⟩
  subst model
  iapply (capture_lookup source columns DFrac.discard Hselector Hcolumns) $$ [Hsource]
  · iframe Hsource
  iintro %result
  imodintro
  iintro ⟨Hresult,_⟩
  iapply HΦ
  iframe Hresult Hsaved

theorem capture_bus_model (model : DivRemFV.CaptureSyntax.Port) (source : BusPort) :
    {{ (InputBusPort model source : IProp GF) }}
      (App (Val (@! busVector)) (Val #source))
    {{ (result : Vector), RET #result; PortValue model result (DFrac.own 1) ∗ InputBusPort model source }} := by
  iintro %Φ #Hmodel HΦ
  ihave #Hsaved := Hmodel
  isimp only [InputBusPort] at Hmodel
  icases Hmodel with ⟨%columns,⟨%Heq,%Hselector,%Hcolumns⟩,Hsource⟩
  subst model
  iapply (capture_bus source columns DFrac.discard Hselector Hcolumns) $$ [Hsource]
  · iframe Hsource
  iintro %result
  imodintro
  iintro ⟨Hresult,_⟩
  iapply HΦ
  iframe Hresult Hsaved

#print axioms capture_lookup_model
#print axioms capture_bus_model
end
end divremfv.internal.airdata.SourceCapture
end Perennial
