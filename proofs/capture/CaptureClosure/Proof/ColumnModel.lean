module
public import CaptureClosure.Proof.ColumnWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

def portableColumn [FfiSyntax] (c : Column) (bits : Option w64) : DivRemFV.CaptureSyntax.Column :=
  ⟨c.ID'.toNat,c.Name'.map BitVec.toNat,bits.map BitVec.toNat,c.Input',c.Output',c.Native'⟩

theorem nameBytes_words (name : GoString) :
    nameBytes name = wireBytes (DivRemFV.CaptureSyntax.natWords (name.map BitVec.toNat)) := by
  simp [nameBytes,wireBytes,DivRemFV.CaptureSyntax.natWords,List.flatMap_map]

theorem boolBytes_words (value : Bool) :
    boolBytes value = wireBytes (DivRemFV.CaptureSyntax.boolWords value) := by
  cases value <;> rfl

theorem optionBytes_words (value : Option w64) :
    optionBytes value = wireBytes (DivRemFV.CaptureSyntax.optionNatWords (value.map BitVec.toNat)) := by
  cases value with
  | none => rfl
  | some value =>
    simp [optionBytes,wireBytes,DivRemFV.CaptureSyntax.optionNatWords,W64]

theorem columnBytes_words [FfiSyntax] (c : Column) (bits : Option w64) :
    columnBytes c bits = wireBytes (portableColumn c bits).words := by
  simp [columnBytes,portableColumn,DivRemFV.CaptureSyntax.Column.words,wireBytes_append,
    nameBytes_words,boolBytes_words,optionBytes_words,wireBytes_cons,wireBytes_nil,W64]

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Column.TypeAssumptions]
variable [FuncUnfold appendWireColumn [] appendWireColumn.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]
variable [FuncUnfold appendWireName [] appendWireName.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]
variable [FuncUnfold appendWireBool [] appendWireBool.impl]

def ColumnValue (model : DivRemFV.CaptureSyntax.Column) (value : Column) (dq : DFrac := DFrac.discard) : IProp GF :=
  iprop(∃ bits : Option w64, ⌜model = portableColumn value bits ∧ value.Name'.length < 2^63⌝ ∗
    OptionalWord value.Bits' bits dq)

instance (model : DivRemFV.CaptureSyntax.Column) (value : Column) :
    Persistent (ColumnValue (GF := GF) model value) := by
  unfold ColumnValue; infer_instance

theorem serialize_column (out : GoSlice) (prior : List w8)
    (model : DivRemFV.CaptureSyntax.Column) (value : Column) (dq : DFrac := DFrac.discard) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ ColumnValue model value dq : IProp GF) }}
      (App (App (Val (@! appendWireColumn)) (Val #out)) (Val #value))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ ColumnValue model value dq }} := by
  iintro %Φ ⟨Hout,Hcap,Hmodel⟩ HΦ
  isimp only [ColumnValue] at Hmodel
  icases Hmodel with ⟨%bits,⟨%Heq,%Hlen⟩,Hbits⟩
  subst model
  iapply append_column_record out prior value bits Hlen dq $$ [Hout Hcap Hbits]
  · iframe Hout Hcap Hbits
  iintro %result
  imodintro
  iintro ⟨Hout,Hcap,Hbits⟩
  iapply HΦ
  rw [← columnBytes_words]
  iframe Hout Hcap
  isimp only [ColumnValue]
  iexists bits
  iframe Hbits
  ipureintro; exact ⟨rfl,Hlen⟩

#print axioms serialize_column
end
end divremfv.internal.airdata.SourceCapture
end Perennial
