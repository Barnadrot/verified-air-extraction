module
public import CaptureClosure.Proof.RowWire
public import CaptureClosure.Proof.ModelBytes

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

theorem rowBytes_words (values : List w64) :
    rowBytes values = wireBytes (DivRemFV.CaptureSyntax.natWords (values.map BitVec.toNat)) := by
  simp [rowBytes,wireBytes,DivRemFV.CaptureSyntax.natWords,List.flatMap_map,W64]

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [FuncUnfold appendWireRows [] appendWireRows.impl]
variable [FuncUnfold appendWireRow [] appendWireRow.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

def RowValue (model : List Nat) (value : GoSlice) (dq : DFrac) : IProp GF :=
  iprop(∃ words : List w64, ⌜model = words.map BitVec.toNat⌝ ∗ value ↦*{dq} words)

abbrev RowsValue (models : List (List Nat)) (values : List GoSlice) (dq : DFrac) : IProp GF :=
  iprop([∗list] k ↦ model;value ∈ models;values, RowValue model value dq)

theorem serialize_row (out : GoSlice) (prior : List w8) (model : List Nat) (value : GoSlice) (dq : DFrac) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ RowValue model value dq : IProp GF) }}
      (App (App (Val (@! appendWireRow)) (Val #out)) (Val #value))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ wireBytes (DivRemFV.CaptureSyntax.natWords model)) ∗
        ownSliceCap w8 result (DFrac.own 1) ∗ RowValue model value dq }} := by
  iintro %Φ ⟨Hout,Hcap,Hmodel⟩ HΦ
  isimp only [RowValue] at Hmodel
  icases Hmodel with ⟨%words,%Heq,Hwords⟩
  subst model
  iapply append_row out prior value words dq $$ [Hout Hcap Hwords]
  · iframe Hout Hcap Hwords
  iintro %result
  imodintro
  iintro ⟨Hout,Hcap,Hwords⟩
  iapply HΦ
  rw [← rowBytes_words]
  iframe Hout Hcap
  isimp only [RowValue]
  iexists words
  iframe Hwords
  ipureintro; rfl

theorem serialize_rows (out : GoSlice) (prior : List w8) (sl : GoSlice)
    (models : List (List Nat)) (values : List GoSlice) (dq : DFrac) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ sl ↦*{dq} values ∗ RowsValue models values dq : IProp GF) }}
      (App (App (Val (@! appendWireRows)) (Val #out)) (Val #sl))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ wireBytes (models.length :: models.flatMap DivRemFV.CaptureSyntax.natWords)) ∗
        ownSliceCap w8 result (DFrac.own 1) ∗ sl ↦*{dq} values ∗ RowsValue models values dq }} := by
  wp_start as ⟨Hout,Hcap,Hsl,Hmodels⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %HmodelLen := BigSepL2.bigSepL2_length $$ Hmodels
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  have Hword : sl.len = W64 models.length := by word
  isimp only [Hword] at Hout
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ current ∗ "row" ∷ row_ptr ↦ last ∗
      "Hout" ∷ current ↦* (prior ++ u64Le (W64 models.length) ++
        wireBytes ((models.take (sint.nat n)).flatMap DivRemFV.CaptureSyntax.natWords)) ∗
      "Hcap" ∷ ownSliceCap w8 current (DFrac.own 1) ∗
      "Hsl" ∷ sl ↦*{dq} values ∗ "Hmodels" ∷ RowsValue models values dq ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝)
      $$ [i out row Hout Hcap Hsl Hmodels]
  · iexists (W64 0),next,slice.nil
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero,List.flatMap_nil,wireBytes_nil,List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < values.length := by word
    have Hmlt : sint.nat n < models.length := by word
    have Hvalue := List.getElem?_eq_getElem Hlt
    have Hmodel := List.getElem?_eq_getElem Hmlt
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1,Hif⟩,
      _root_.and_self,ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) values dq values[sint.nat n] Hn.1 $$ [Hsl] with Hsl
    · iframe Hsl; ipureintro; exact Hvalue
    ihave ⟨Hchild,Hrestore⟩ := BigSepL2.bigSepL2_lookup_acc Hmodel Hvalue $$ Hmodels
    wp_apply (serialize_row _ _ models[sint.nat n] values[sint.nat n] dq)
      $$ [Hout Hcap Hchild] with %result ⟨Hout,Hcap,Hchild⟩
    · iframe Hout Hcap Hchild
    ihave Hmodels := Hrestore $$ Hchild
    wp_for_post
    iframe
    iexists (n + W64 1),result,values[sint.nat n]
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hstep,List.take_add_one,Hmodel]
    simp only [Option.toList_some,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,wireBytes_append,List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = models.length := by word
    isimp only [Heq,List.take_length] at Hout
    iapply HΦ
    simp only [wireBytes_cons,List.append_assoc]
    iframe Hout Hcap Hsl Hmodels

#print axioms serialize_row
#print axioms serialize_rows
end
end divremfv.internal.airdata.SourceCapture
end Perennial
