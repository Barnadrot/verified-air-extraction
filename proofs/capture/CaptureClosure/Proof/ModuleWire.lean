module
public import CaptureClosure.Proof.ColumnsWire
public import CaptureClosure.Proof.RowsWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

def portableModule [FfiSyntax] (value : Module) (columns : List DivRemFV.CaptureSyntax.Column)
    (content : List (List Nat)) : DivRemFV.CaptureSyntax.Module :=
  ⟨value.ID'.toNat,value.Name'.map BitVec.toNat,value.Static',value.Native',columns,content⟩

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

def ModuleValue (model : DivRemFV.CaptureSyntax.Module) (value : Module) (dq : DFrac) : IProp GF :=
  iprop(∃ (columns : List DivRemFV.CaptureSyntax.Column) (rows : List (List Nat))
      (columnValues : List Column) (rowValues : List GoSlice),
    ⌜model = portableModule value columns rows ∧ value.Name'.length < 2^63⌝ ∗
    value.Columns' ↦*{dq} columnValues ∗ ColumnsValue columns columnValues dq ∗
    value.Content' ↦*{dq} rowValues ∗ RowsValue rows rowValues dq)

variable [Module.TypeAssumptions] [Column.TypeAssumptions]
variable [FuncUnfold appendWireModule [] appendWireModule.impl]
variable [FuncUnfold appendWireColumns [] appendWireColumns.impl]
variable [FuncUnfold appendWireColumn [] appendWireColumn.impl]
variable [FuncUnfold appendWireRows [] appendWireRows.impl]
variable [FuncUnfold appendWireRow [] appendWireRow.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]
variable [FuncUnfold appendWireName [] appendWireName.impl]
variable [FuncUnfold appendWireBool [] appendWireBool.impl]

theorem serialize_module (out : GoSlice) (prior : List w8)
    (model : DivRemFV.CaptureSyntax.Module) (value : Module) (dq : DFrac) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ ModuleValue model value dq : IProp GF) }}
      (App (App (Val (@! appendWireModule)) (Val #out)) (Val #value))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ ModuleValue model value dq }} := by
  wp_start as ⟨Hout,Hcap,Hmodel⟩
  isimp only [ModuleValue] at Hmodel
  icases Hmodel with ⟨%columns,%rows,%columnValues,%rowValues,⟨%Heq,%Hlen⟩,Hcolumns,HcolumnModels,Hrows,HrowModels⟩
  subst model
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply (append_name _ _ value.Name' Hlen) $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_bool $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_bool $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply (serialize_columns _ _ value.Columns' columns columnValues dq)
    $$ [Hout Hcap Hcolumns HcolumnModels] with %next ⟨Hout,Hcap,Hcolumns,HcolumnModels⟩
  · iframe Hout Hcap Hcolumns HcolumnModels
  wp_apply (serialize_rows _ _ value.Content' rows rowValues dq)
    $$ [Hout Hcap Hrows HrowModels] with %result ⟨Hout,Hcap,Hrows,HrowModels⟩
  · iframe Hout Hcap Hrows HrowModels
  iapply HΦ
  simp only [portableModule,DivRemFV.CaptureSyntax.Module.words,wireBytes_append,wireBytes_cons,
    wireBytes_nil,nameBytes_words,boolBytes_words,List.append_nil,List.append_assoc]
  have Hid : W64 value.ID'.toNat = value.ID' := by word
  rw [Hid]
  try isimp only [List.append_assoc] at Hout
  iframe Hout Hcap
  isimp only [ModuleValue]
  iexists columns,rows,columnValues,rowValues
  iframe Hcolumns HcolumnModels Hrows HrowModels
  ipureintro; exact ⟨rfl,Hlen⟩

#print axioms serialize_module
end
end divremfv.internal.airdata.SourceCapture
end Perennial
