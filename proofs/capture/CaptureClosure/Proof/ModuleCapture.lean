module
public import CaptureClosure.Proof.ColumnsCapture
public import CaptureClosure.Proof.RowsCapture
public import CaptureClosure.Proof.ModuleWire
public import CaptureClosure.Proof.TableReads

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.schema
open github_com.LFDT_Lineth.zkc.pkg.schema.register
local notation "FType" => github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty
local notation "CType" => github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.ty FType
local notation "SourceTable" => Table (GoArray w32 1) GoInterface

structure TableData [FfiSyntax] where
  name : GoString
  isStatic : Bool
  isNative : Bool
  registers : List Register
  rows : List (List w32)

def tableModel [FfiSyntax] (id : w64) (data : TableData) (inputTag outputTag : Type') :
    DivRemFV.CaptureSyntax.Module :=
  ⟨id.toNat,data.name.map BitVec.toNat,data.isStatic,data.isNative,
    registerColumns data.registers inputTag outputTag,
    if data.isStatic then capturedRows data.rows else []⟩

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

def InputModule (data : TableData) (p : Loc) : IProp GF :=
  iprop(∃ (registers rows : GoSlice) (rowSlices : List GoSlice),
    ⌜p ≠ null ∧ data.name.length < 2^63 ∧ (∀ value ∈ data.registers, value.name'.length < 2^63)⌝ ∗
    p.[SourceTable,go!"name"] ↦□ data.name ∗
    p.[SourceTable,go!"static"] ↦□ data.isStatic ∗
    p.[SourceTable,go!"native"] ↦□ data.isNative ∗
    p.[SourceTable,go!"registers"] ↦□ registers ∗ registers ↦*□ data.registers ∗
    p.[SourceTable,go!"staticContents"] ↦□ rows ∗ rows ↦*□ rowSlices ∗
    InputRows data.rows rowSlices DFrac.discard)

instance (data : TableData) (p : Loc) : Persistent (InputModule (GF := GF) data p) := by
  unfold InputModule
  infer_instance

variable [Module.TypeAssumptions] [Column.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.TypeAssumptions]
variable [Table.TypeAssumptions] [github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.register.«Type».TypeAssumptions] [Register.TypeAssumptions]
variable [FuncUnfold exportModule [] exportModule.impl]
variable [FuncUnfold exportColumns [] exportColumns.impl]
variable [FuncUnfold exportColumn [] exportColumn.impl]
variable [FuncUnfold exportStaticRows [] exportStaticRows.impl]
variable [FuncUnfold exportStaticRow [] exportStaticRow.impl]
variable [FuncUnfold github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce []
  github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce.impl]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]

theorem capture_module (id : w64) (data : TableData) (p : Loc) (inputTag outputTag : Type') :
    {{ (InputModule data p ∗ globalAddr INPUT_REGISTER ↦□ inputTag ∗
        globalAddr OUTPUT_REGISTER ↦□ outputTag : IProp GF) }}
      (App (App (Val (@! exportModule)) (Val #id)) (Val #p))
    {{ (result : Module), RET #result;
      ModuleValue (tableModel id data inputTag outputTag) result (DFrac.own 1) }} := by
  wp_start as ⟨#Hsource,#Hinput,#Houtput⟩
  iunfold InputModule at Hsource
  icases Hsource with ⟨%registers,%rows,%rowSlices,⟨%Hnonnull,%HnameLen,%HregisterBounds⟩,
    #Hname,#Hstatic,#Hnative,#HregisterField,#Hregisters,#HrowField,#Hrows,#HrowInputs⟩
  wp_auto
  wp_apply (Table.name_correct FType CType p data.name DFrac.discard Hnonnull)
    with _
  · iframe Hname
  wp_apply (Table.isStatic_correct FType CType p data.isStatic DFrac.discard Hnonnull)
    with _
  · iframe Hstatic
  wp_apply (Table.isNative_correct FType CType p data.isNative DFrac.discard Hnonnull)
    with _
  · iframe Hnative
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Column.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Column) (t := Column.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %emptyColumns ⟨HemptyColumns,HemptyColumnCap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.SliceType go.uint64))))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := GoSlice) (t := go.SliceType go.uint64) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %emptyRows ⟨HemptyRows,HemptyRowCap⟩
  wp_auto
  wp_apply (Table.registers_correct FType CType p registers DFrac.discard Hnonnull) with _
  · iframe HregisterField
  wp_apply (capture_columns registers data.registers inputTag outputTag DFrac.discard HregisterBounds)
    with %columns ⟨%columnValues,Hcolumns,HcolumnCap,HcolumnModels,_⟩
  · iframe Hregisters Hinput Houtput
  wp_apply (Table.isStatic_correct FType CType p data.isStatic DFrac.discard Hnonnull) with _
  · iframe Hstatic
  cases Hflag : data.isStatic with
  | false =>
    try wp_auto
    iapply HΦ
    isimp only [ModuleValue]
    iexists registerColumns data.registers inputTag outputTag,[],columnValues,[]
    iframe Hcolumns HcolumnModels HemptyRows
    isplitl []
    · ipureintro; exact ⟨by simp [tableModel,portableModule,Hflag],HnameLen⟩
    iapply BigSepL2.bigSepL2_nil.2; itrivial
  | true =>
    try wp_auto
    wp_apply (Table.staticContents_correct FType CType p rows DFrac.discard Hnonnull) with _
    · try isimp only [Hflag] at Hstatic
      iframe Hstatic HrowField
    wp_apply (capture_rows rows data.rows rowSlices DFrac.discard)
      with %content ⟨%rowValues,Hcontent,HcontentCap,HrowModels,_,_⟩
    · iframe Hrows HrowInputs
    iapply HΦ
    isimp only [ModuleValue]
    iexists registerColumns data.registers inputTag outputTag,capturedRows data.rows,columnValues,rowValues
    iframe Hcolumns HcolumnModels Hcontent HrowModels
    ipureintro; exact ⟨by simp [tableModel,portableModule,Hflag],HnameLen⟩

#print axioms capture_module
end
end divremfv.internal.airdata.SourceCapture
end Perennial
