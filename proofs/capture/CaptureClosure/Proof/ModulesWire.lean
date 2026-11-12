module
public import CaptureClosure.Proof.ModuleWire

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
variable [Module.TypeAssumptions] [Column.TypeAssumptions]
variable [FuncUnfold appendWireModule [] appendWireModule.impl]
variable [FuncUnfold appendWireColumns [] appendWireColumns.impl]
variable [FuncUnfold appendWireColumn [] appendWireColumn.impl]
variable [FuncUnfold appendWireRows [] appendWireRows.impl]
variable [FuncUnfold appendWireRow [] appendWireRow.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]
variable [FuncUnfold appendWireName [] appendWireName.impl]
variable [FuncUnfold appendWireBool [] appendWireBool.impl]
variable [FuncUnfold appendWireModules [] appendWireModules.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

abbrev ModulesValue (models : List DivRemFV.CaptureSyntax.Module) (values : List Module) (dq : DFrac) : IProp GF :=
  iprop([∗list] _k ↦ model;value ∈ models;values, ModuleValue model value dq)

theorem serialize_modules (out : GoSlice) (prior : List w8) (sl : GoSlice)
    (models : List DivRemFV.CaptureSyntax.Module) (values : List Module) (dq : DFrac) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ sl ↦*{dq} values ∗ ModulesValue models values dq : IProp GF) }}
      (App (App (Val (@! appendWireModules)) (Val #out)) (Val #sl))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ wireBytes (models.length :: models.flatMap DivRemFV.CaptureSyntax.Module.words)) ∗
        ownSliceCap w8 result (DFrac.own 1) ∗ sl ↦*{dq} values ∗ ModulesValue models values dq }} := by
  wp_start as ⟨Hout,Hcap,Hsl,Hmodels⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %HmodelLen := BigSepL2.bigSepL2_length $$ Hmodels
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  have Hword : sl.len = W64 models.length := by word
  isimp only [Hword] at Hout
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : Module),
      "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ current ∗ "m" ∷ m_ptr ↦ last ∗
      "Hout" ∷ current ↦* (prior ++ u64Le (W64 models.length) ++
        wireBytes ((models.take (sint.nat n)).flatMap DivRemFV.CaptureSyntax.Module.words)) ∗
      "Hcap" ∷ ownSliceCap w8 current (DFrac.own 1) ∗
      "Hsl" ∷ sl ↦*{dq} values ∗ "Hmodels" ∷ ModulesValue models values dq ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝)
      $$ [i out m Hout Hcap Hsl Hmodels]
  · iexists (W64 0),next,zero_val Module
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
    wp_apply (serialize_module _ _ models[sint.nat n] values[sint.nat n] dq)
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

#print axioms serialize_modules
end
end divremfv.internal.airdata.SourceCapture
end Perennial
