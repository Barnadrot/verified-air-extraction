module
public import CaptureClosure.Proof.ArtifactBounds
public import CaptureClosure.Proof.ByteContract

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

def WireResult (model : DivRemFV.CaptureSyntax.Artifact) (result : GoSlice) : IProp GF :=
  iprop(result ↦* wireBytes model.words ∗ ownSliceCap w8 result (DFrac.own 1) ∗
    ⌜WordsBounded model.words ∧ (wireBytes model.words).map BitVec.toNat = DivRemFV.CaptureSyntax.byteValues model.words⌝)

variable [Artifact.TypeAssumptions] [Module.TypeAssumptions] [Column.TypeAssumptions]
variable [Constraint.TypeAssumptions] [Term.TypeAssumptions] [Vector.TypeAssumptions]
variable [FuncUnfold EncodeArtifactWire [] EncodeArtifactWire.impl]
variable [FuncUnfold appendWireModules [] appendWireModules.impl]
variable [FuncUnfold appendWireModule [] appendWireModule.impl]
variable [FuncUnfold appendWireColumns [] appendWireColumns.impl]
variable [FuncUnfold appendWireColumn [] appendWireColumn.impl]
variable [FuncUnfold appendWireRows [] appendWireRows.impl]
variable [FuncUnfold appendWireRow [] appendWireRow.impl]
variable [FuncUnfold appendWireConstraints [] appendWireConstraints.impl]
variable [FuncUnfold appendWireConstraint [] appendWireConstraint.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]
variable [FuncUnfold appendWireName [] appendWireName.impl]
variable [FuncUnfold appendWireBool [] appendWireBool.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]
variable [FuncUnfold appendWireDomain [] appendWireDomain.impl]
variable [FuncUnfold appendWireFramedTerm [] appendWireFramedTerm.impl]
variable [FuncUnfold EncodeTermWire [] EncodeTermWire.impl]
variable [FuncUnfold appendTermWire [] appendTermWire.impl]
variable [FuncUnfold appendArgsWire [] appendArgsWire.impl]
variable [FuncUnfold appendWirePorts [] appendWirePorts.impl]
variable [FuncUnfold appendWirePort [] appendWirePort.impl]

theorem serialize_checked_artifact (model : DivRemFV.CaptureSyntax.Artifact) (value : Artifact) (dq : DFrac) :
    {{ (ArtifactValue model value dq : IProp GF) }}
      (App (Val (@! EncodeArtifactWire)) (Val #value))
    {{ (result : GoSlice), RET (PairV #result #interface.nil); WireResult model result }} := by
  iintro %Φ Hmodel HΦ
  iapply (serialize_artifact model value dq) $$ [Hmodel]
  · iframe Hmodel
  iintro %result
  imodintro
  iintro ⟨Hbytes,Hcap,Hmodel⟩
  ihave %Hlen := ownSlice_len $$ Hbytes
  rw [wireBytes_length] at Hlen
  have Hsize : model.words.length < 2^64 := by word
  ihave %Hbounds := artifact_bounded model value dq Hsize $$ Hmodel
  iapply HΦ
  isimp only [WireResult]
  iframe Hbytes Hcap
  ipureintro
  exact ⟨Hbounds,all_byte_values model.words Hbounds⟩

#print axioms serialize_checked_artifact
end
end divremfv.internal.airdata.SourceCapture
end Perennial
