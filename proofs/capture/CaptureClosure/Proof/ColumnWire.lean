module
public import CaptureClosure.Proof.RecordLayouts
public import CaptureClosure.Proof.SimpleWire
public import CaptureClosure.Proof.NameWire
public import CaptureClosure.Proof.ModelBytes

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
variable [FuncUnfold appendWireWord [] appendWireWord.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]

def OptionalWord (p : Loc) (value : Option w64) (dq : DFrac := DFrac.discard) : IProp GF := match value with
  | none => iprop(⌜p = null⌝)
  | some value => iprop(⌜p ≠ null⌝ ∗ p ↦{dq} value)

instance (p : Loc) (value : Option w64) : Persistent (OptionalWord (GF := GF) p value) := by
  cases value <;> simp only [OptionalWord] <;> infer_instance

def optionBytes : Option w64 → List w8
  | none => u64Le (W64 0) ++ u64Le (W64 0)
  | some value => u64Le (W64 1) ++ u64Le value

theorem append_option (out : GoSlice) (prior : List w8) (p : Loc) (value : Option w64) (dq : DFrac := DFrac.discard) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OptionalWord p value dq : IProp GF) }}
      (App (App (Val (@! appendWireOption)) (Val #out)) (Val #p))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ optionBytes value) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OptionalWord p value dq }} := by
  iintro %Φ ⟨Hout,Hcap,Hvalue⟩ HΦ
  cases value with
  | none =>
    isimp only [OptionalWord] at Hvalue
    icases Hvalue with %Hp
    subst p
    iapply append_option_none out prior $$ [Hout Hcap]
    · iframe Hout Hcap
    iintro %result
    imodintro
    iintro ⟨Hout,Hcap⟩
    iapply HΦ
    simp only [optionBytes,List.append_assoc]
    try isimp only [List.append_assoc] at Hout
    iframe Hout Hcap
    isimp only [OptionalWord]
    ipureintro; trivial
  | some value =>
    isimp only [OptionalWord] at Hvalue
    icases Hvalue with ⟨%Hp,Hpoint⟩
    iapply append_option_some_frac out prior p value dq Hp $$ [Hout Hcap Hpoint]
    · iframe Hout Hcap Hpoint
    iintro %result
    imodintro
    iintro ⟨Hout,Hcap,Hpoint⟩
    iapply HΦ
    simp only [optionBytes,List.append_assoc]
    try isimp only [List.append_assoc] at Hout
    iframe Hout Hcap
    isimp only [OptionalWord]
    iframe Hpoint
    ipureintro; exact Hp

def columnBytes (c : Column) (bits : Option w64) : List w8 :=
  u64Le c.ID' ++ nameBytes c.Name' ++ optionBytes bits ++ boolBytes c.Input' ++
    boolBytes c.Output' ++ boolBytes c.Native'

variable [Column.TypeAssumptions]
variable [FuncUnfold appendWireColumn [] appendWireColumn.impl]
variable [FuncUnfold appendWireName [] appendWireName.impl]
variable [FuncUnfold appendWireBool [] appendWireBool.impl]

theorem append_column_record (out : GoSlice) (prior : List w8) (c : Column) (bits : Option w64)
    (bounded : c.Name'.length < 2^63) (dq : DFrac := DFrac.discard) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OptionalWord c.Bits' bits dq : IProp GF) }}
      (App (App (Val (@! appendWireColumn)) (Val #out)) (Val #c))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ columnBytes c bits) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OptionalWord c.Bits' bits dq }} := by
  wp_start as ⟨Hout,Hcap,Hbits⟩
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply (append_name _ _ c.Name' bounded) $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply (append_option _ _ c.Bits' bits dq) $$ [Hout Hcap Hbits] with %next ⟨Hout,Hcap,Hbits⟩
  · iframe Hout Hcap Hbits
  wp_apply append_bool $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_bool $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_bool $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  iapply HΦ
  simp only [columnBytes]
  simp only [List.append_assoc] at *
  iframe Hout Hcap Hbits

#print axioms append_option
#print axioms append_column_record
end
end divremfv.internal.airdata.SourceCapture
end Perennial
