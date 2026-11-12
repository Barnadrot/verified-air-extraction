module
public import CaptureClosure.Proof.ModulesCapture
public import CaptureClosure.Proof.AllConstraintsCapture
public import CaptureClosure.Proof.SchemaReads
public import CaptureClosure.Proof.ArtifactWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.schema
open github_com.LFDT_Lineth.zkc.pkg.schema.register
local notation "FType" => github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty
local notation "CType" => github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.ty FType
local notation "TableType" => github_com.LFDT_Lineth.zkc.pkg.schema.Table.ty FType CType
local notation "SourceSchema" => UniformSchema (GoArray w32 1) Loc

def schemaModel [FfiSyntax] (tables : List TableData) (entries : List (List DivRemFV.CaptureSyntax.Entry))
    (inputTag outputTag : Type') : DivRemFV.CaptureSyntax.Artifact :=
  ⟨tableModels tables inputTag outputTag,entries.flatten⟩

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

def InputSchema (modelTables : List TableData) (modelEntries : List (List DivRemFV.CaptureSyntax.Entry))
    (schema : SourceSchema) : IProp GF :=
  iprop(∃ sources : List Loc, schema.modules' ↦*□ sources ∗
    InputModules modelTables sources ∗ InputAllEntries modelEntries sources)

instance (tables : List TableData) (entries : List (List DivRemFV.CaptureSyntax.Entry)) (schema : SourceSchema) :
    Persistent (InputSchema (GF := GF) tables entries schema) := by unfold InputSchema; infer_instance

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

theorem capture_artifact (tables : List TableData) (entries : List (List DivRemFV.CaptureSyntax.Entry))
    (schema : SourceSchema) (inputTag outputTag : Type') :
    {{ (InputSchema tables entries schema ∗ globalAddr INPUT_REGISTER ↦□ inputTag ∗
        globalAddr OUTPUT_REGISTER ↦□ outputTag : IProp GF) }}
      (App (Val (@! Export)) (Val #schema))
    {{ (result : Artifact), RET (PairV #result #interface.nil);
      ArtifactValue (schemaModel tables entries inputTag outputTag) result (DFrac.own 1) }} := by
  wp_start as ⟨#Hsource,#Hinput,#Houtput⟩
  iunfold InputSchema at Hsource
  icases Hsource with ⟨%sources,#Hsources,#HmoduleInputs,#HconstraintInputs⟩
  try wp_auto
  wp_apply (UniformSchema.rawModules_correct FType (go.PointerType TableType) schema)
  all_goals try itrivial
  wp_apply (capture_modules schema.modules' tables sources inputTag outputTag)
    with %moduleSlice ⟨%modules,Hmodules,HmoduleCap,HmoduleModels⟩
  · iframe Hsources HmoduleInputs Hinput Houtput
  wp_apply (UniformSchema.rawModules_correct FType (go.PointerType TableType) schema)
  all_goals try itrivial
  wp_apply (capture_all_constraints schema.modules' entries sources)
    with %constraintSlice ⟨%constraints,Hconstraints,HconstraintCap,HconstraintModels⟩
  · iframe Hsources HconstraintInputs
  iapply HΦ
  isimp only [ArtifactValue,schemaModel]
  iexists modules,constraints
  iframe Hmodules HmoduleModels Hconstraints HconstraintModels
  ipureintro; exact ⟨True.intro,True.intro,True.intro⟩

#print axioms capture_artifact
end
end divremfv.internal.airdata.SourceCapture
end Perennial
