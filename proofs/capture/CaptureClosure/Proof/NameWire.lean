module
public import CaptureClosure.Proof.WordWire

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
variable [FuncUnfold appendWireName [] appendWireName.impl]

def nameBytes (value : GoString) : List w8 :=
  u64Le (W64 value.length) ++ value.flatMap (fun byte => u64Le (W64 byte.toNat))

theorem append_name (out : GoSlice) (prior : List w8) (value : GoString)
    (bounded : value.length < 2^63) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! appendWireName)) (Val #out)) (Val #value))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ nameBytes value) ∗ ownSliceCap w8 result (DFrac.own 1) }} := by
  wp_start as ⟨Hout,Hcap⟩
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hlen
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  ihave IH : iprop(∃ (n : w64) (current : GoSlice),
      "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ current ∗
      "Hout" ∷ current ↦* (prior ++ u64Le (W64 value.length) ++
        (value.take (sint.nat n)).flatMap (fun byte => u64Le (W64 byte.toNat))) ∗
      "Hcap" ∷ ownSliceCap w8 current (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (value.length : Int)⌝) $$ [i out Hout Hcap]
  · iexists (W64 0),next
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero,List.flatMap_nil,List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  wp_if_destruct
  · have Htest := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < value.length := by word
    have Hindex := List.getElem?_eq_getElem Hlt
    rw [ite_eq_left (show 0 ≤ sint.Z n by word), Hindex]
    wp_auto
    wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_for_post
    iframe
    iexists (n + W64 1),result
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hstep,List.take_add_one,Hindex,List.flatMap_append]
    simp only [Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  · have Htest : ¬ sint.Z n < sint.Z (W64 value.length) := by
      intro h
      apply Hif
      simp only [decide_eq_true h]
    simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = value.length := by word
    wp_auto
    iapply HΦ
    isimp only [Heq,List.take_length] at Hout
    unfold nameBytes
    rw [← List.append_assoc]
    iframe Hout Hcap

#print axioms append_name
end
end divremfv.internal.airdata.SourceCapture
end Perennial
