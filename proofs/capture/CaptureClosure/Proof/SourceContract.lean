module
public import CaptureClosure.Proof.ArtifactCapture
public import CaptureClosure.Proof.CheckedWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.schema
open github_com.LFDT_Lineth.zkc.pkg.schema.register
local notation "SourceSchema" => UniformSchema (GoArray w32 1) Loc
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [Artifact.TypeAssumptions] [Module.TypeAssumptions] [Column.TypeAssumptions]
variable [Constraint.TypeAssumptions] [Term.TypeAssumptions] [Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.LogicalTerm.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Add.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.Table.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.UniformSchema.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.register.«Type».TypeAssumptions] [Register.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.TypeAssumptions]
variable [FuncUnfold Export [] Export.impl]
variable [FuncUnfold exportModules [] exportModules.impl]
variable [FuncUnfold exportModule [] exportModule.impl]
variable [FuncUnfold exportColumns [] exportColumns.impl]
variable [FuncUnfold exportColumn [] exportColumn.impl]
variable [FuncUnfold exportStaticRows [] exportStaticRows.impl]
variable [FuncUnfold exportStaticRow [] exportStaticRow.impl]
variable [FuncUnfold exportAllConstraints [] exportAllConstraints.impl]
variable [FuncUnfold exportModuleConstraints [] exportModuleConstraints.impl]
variable [FuncUnfold exportConstraint [] exportConstraint.impl]
variable [FuncUnfold exportDomain [] exportDomain.impl]
variable [FuncUnfold exportLookupVectors [] exportLookupVectors.impl]
variable [FuncUnfold exportBusPorts [] exportBusPorts.impl]
variable [FuncUnfold lookupVector [] lookupVector.impl]
variable [FuncUnfold busVector [] busVector.impl]
variable [FuncUnfold uintRef [] uintRef.impl]
variable [FuncUnfold exportColumnIDs [] exportColumnIDs.impl]
variable [FuncUnfold ExportTerm [] ExportTerm.impl]
variable [FuncUnfold github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce []
  github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce.impl]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]
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

theorem capture_to_checked_wire (tables : List TableData) (entries : List (List DivRemFV.CaptureSyntax.Entry))
    (schema : SourceSchema) (inputTag outputTag : Type') :
    {{ (InputSchema tables entries schema ∗ globalAddr INPUT_REGISTER ↦□ inputTag ∗
        globalAddr OUTPUT_REGISTER ↦□ outputTag : IProp GF) }}
      (App (Val (@! Export)) (Val #schema))
    {{ (artifact : Artifact), RET (PairV #artifact #interface.nil);
      WP (App (Val (@! EncodeArtifactWire)) (Val #artifact))
        {{ value, ∃ result : GoSlice, ⌜value = PairV #result #interface.nil⌝ ∗
          WireResult (schemaModel tables entries inputTag outputTag) result }} }} := by
  iintro %Φ ⟨Hsource,Hinput,Houtput⟩ HΦ
  iapply (capture_artifact tables entries schema inputTag outputTag) $$ [Hsource Hinput Houtput]
  · iframe Hsource Hinput Houtput
  iintro %artifact
  imodintro
  iintro Hcaptured
  iapply HΦ
  iapply (serialize_checked_artifact (schemaModel tables entries inputTag outputTag) artifact (DFrac.own 1)) $$ [Hcaptured]
  · iframe Hcaptured
  iintro %result
  imodintro
  iintro Hwire
  iexists result
  iframe Hwire
  ipureintro; rfl

#print axioms capture_to_checked_wire
end
end divremfv.internal.airdata.SourceCapture
end Perennial
