module
public import CaptureClosure.Proof.ModulesWire
public import CaptureClosure.Proof.ConstraintsWire

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

def ArtifactValue (model : DivRemFV.CaptureSyntax.Artifact) (value : Artifact) (dq : DFrac) : IProp GF :=
  iprop(∃ (modules : List Module) (constraints : List Constraint),
    ⌜value.Format' = go!"divrem-air-v1" ∧ value.Field' = go!"KOALABEAR_16" ∧ value.Modulus' = W64 2130706433⌝ ∗
    value.Modules' ↦*{dq} modules ∗ ModulesValue model.modules modules dq ∗
    value.Constraints' ↦*{dq} constraints ∗ ConstraintsValue model.entries constraints dq)

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

theorem serialize_artifact (model : DivRemFV.CaptureSyntax.Artifact) (value : Artifact) (dq : DFrac) :
    {{ (ArtifactValue model value dq : IProp GF) }}
      (App (Val (@! EncodeArtifactWire)) (Val #value))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* wireBytes model.words ∗ ownSliceCap w8 result (DFrac.own 1) ∗ ArtifactValue model value dq }} := by
  wp_start as Hmodel
  isimp only [ArtifactValue] at Hmodel
  icases Hmodel with ⟨%modules,%constraints,⟨%Hformat,%Hfield,%Hmodulus⟩,Hmodules,HmoduleModels,Hconstraints,HconstraintModels⟩
  wp_auto
  rw [Hformat]
  wp_auto
  rw [Hfield]
  wp_auto
  rw [Hmodulus]
  wp_auto
  wp_apply (append_word slice.nil [] (W64 1146242647)) with %next ⟨Hout,Hcap⟩
  · isplitl []
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply (serialize_modules _ _ value.Modules' model.modules modules dq)
    $$ [Hout Hcap Hmodules HmoduleModels] with %next ⟨Hout,Hcap,Hmodules,HmoduleModels⟩
  · iframe Hout Hcap Hmodules HmoduleModels
  wp_apply (serialize_constraints _ _ value.Constraints' model.entries constraints dq)
    $$ [Hout Hcap Hconstraints HconstraintModels] with %result ⟨Hout,Hcap,Hconstraints,HconstraintModels⟩
  · iframe Hout Hcap Hconstraints HconstraintModels
  iapply HΦ
  simp only [DivRemFV.CaptureSyntax.Artifact.words,DivRemFV.CaptureSyntax.modulus,wireBytes_append,
    wireBytes_cons,wireBytes_nil,List.append_nil,List.nil_append,List.append_assoc]
  try isimp only [List.append_assoc,List.nil_append] at Hout
  iframe Hout Hcap
  isimp only [ArtifactValue]
  iexists modules,constraints
  iframe Hmodules HmoduleModels Hconstraints HconstraintModels
  ipureintro; exact ⟨Hformat,Hfield,Hmodulus⟩

#print axioms serialize_artifact
end
end divremfv.internal.airdata.SourceCapture
end Perennial
