module
public import CaptureClosure.Proof.PortWire
public import CaptureClosure.Proof.ColumnModel

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

def portablePort [FfiSyntax] (port : Vector) (selector : Option w64) (columns : List w64) :
    DivRemFV.CaptureSyntax.Port :=
  ⟨port.Module'.toNat,selector.map BitVec.toNat,columns.map BitVec.toNat⟩

theorem portBytes_words [FfiSyntax] (port : Vector) (selector : Option w64) (columns : List w64) :
    portBytes port selector columns = wireBytes (portablePort port selector columns).words := by
  simp [portBytes,portablePort,DivRemFV.CaptureSyntax.Port.words,DivRemFV.CaptureSyntax.natWords,
    wireBytes_append,wireBytes_cons,wireBytes_nil,optionBytes_words,wireBytes,List.flatMap_map,W64]

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Vector.TypeAssumptions]
variable [FuncUnfold appendWirePort [] appendWirePort.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]

def PortValue (model : DivRemFV.CaptureSyntax.Port) (value : Vector) (dq : DFrac) : IProp GF :=
  iprop(∃ (selector : Option w64) (columns : List w64),
    ⌜model = portablePort value selector columns⌝ ∗
    OptionalWord value.Selector' selector dq ∗ value.Columns' ↦*{dq} columns)

theorem serialize_port (out : GoSlice) (prior : List w8)
    (model : DivRemFV.CaptureSyntax.Port) (value : Vector) (dq : DFrac) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ PortValue model value dq : IProp GF) }}
      (App (App (Val (@! appendWirePort)) (Val #out)) (Val #value))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ PortValue model value dq }} := by
  iintro %Φ ⟨Hout,Hcap,Hmodel⟩ HΦ
  isimp only [PortValue] at Hmodel
  icases Hmodel with ⟨%selector,%columns,%Heq,Hselector,Hcolumns⟩
  subst model
  iapply append_port out prior value selector columns dq $$ [Hout Hcap Hselector Hcolumns]
  · iframe Hout Hcap Hselector Hcolumns
  iintro %result
  imodintro
  iintro ⟨Hout,Hcap,Hselector,Hcolumns⟩
  iapply HΦ
  rw [← portBytes_words]
  iframe Hout Hcap
  isimp only [PortValue]
  iexists selector,columns
  iframe Hselector Hcolumns
  ipureintro; rfl

#print axioms serialize_port
end
end divremfv.internal.airdata.SourceCapture
end Perennial
