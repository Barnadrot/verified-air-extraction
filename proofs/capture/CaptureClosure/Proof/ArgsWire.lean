module
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
variable [sem : go.Semantics] [Term.TypeAssumptions]
variable [FuncUnfold appendArgsWire [] appendArgsWire.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

theorem append_args (out : GoSlice) (prior : List w8) (sl : GoSlice) (dq : DFrac)
    (models : List ModelTerm) (values : List Term)
    (calls : ∀ model ∈ models, ∀ (out : GoSlice) (prior : List w8) (value : Term),
      ⊢ iprop({{ out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OutputTerm (GF := GF) model value }}
        (App (App (Val (@! appendTermWire)) (Val #out)) (Val #value))
        {{ (result : GoSlice), RET (PairV #result #interface.nil);
          result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OutputTerm model value }})) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗
        sl ↦*{dq} values ∗ OutputList models values : IProp GF) }}
      (App (App (Val (@! appendArgsWire)) (Val #out)) (Val #sl))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* (prior ++ wireBytes (argStream models ++ [0])) ∗ ownSliceCap w8 result (DFrac.own 1) ∗
      sl ↦*{dq} values ∗ OutputList models values }} := by
  wp_start as ⟨Hout,Hcap,Hsl,Hmodels⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave %HmodelLen := BigSepL2.bigSepL2_length $$ Hmodels
  wp_auto
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : Term),
      "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ current ∗ "arg" ∷ arg_ptr ↦ last ∗
      "Hout" ∷ current ↦* (prior ++ wireBytes (argStream (models.take (sint.nat n)))) ∗
      "Hcap" ∷ ownSliceCap w8 current (DFrac.own 1) ∗
      "Hsl" ∷ sl ↦*{dq} values ∗ "Hmodels" ∷ OutputList models values ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝)
      $$ [i out arg Hout Hcap Hsl Hmodels]
  · iexists (W64 0),out,zero_val Term
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero,argStream,List.flatMap_nil,
      wireBytes_nil,List.append_nil]
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
    wp_apply wp_load_slice_index sl (sint.Z n) values dq values[sint.nat n] Hn.1
      $$ [Hsl] with Hsl
    · iframe Hsl; ipureintro; exact Hvalue
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    ihave ⟨Hchild,Hrestore⟩ := BigSepL2.bigSepL2_lookup_acc Hmodel Hvalue $$ Hmodels
    wp_apply (calls models[sint.nat n] (List.mem_of_getElem? Hmodel) _ _ _)
      $$ [Hout Hcap Hchild] with %result ⟨Hout,Hcap,Hchild⟩
    · iframe Hout Hcap Hchild
    ihave Hmodels := Hrestore $$ Hchild
    wp_for_post
    iframe
    iexists (n + W64 1),result,values[sint.nat n]
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hstep,List.take_add_one,Hmodel]
    simp only [Option.toList_some,argStream,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,wireBytes_append,wireBytes_cons,wireBytes_nil,List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = models.length := by word
    isimp only [Heq,List.take_length] at Hout
    wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    iapply HΦ
    simp only [wireBytes_append,wireBytes_cons,wireBytes_nil,List.append_nil,List.append_assoc]
    iframe Hout Hcap Hsl Hmodels

end
end divremfv.internal.airdata.SourceCapture
end Perennial
