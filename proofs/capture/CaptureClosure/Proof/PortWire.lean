module
public import CaptureClosure.Proof.ColumnWire

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Vector.TypeAssumptions]
variable [FuncUnfold appendWirePort [] appendWirePort.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]

def portBytes (port : Vector) (selector : Option w64) (columns : List w64) : List w8 :=
  u64Le port.Module' ++ optionBytes selector ++ u64Le (W64 columns.length) ++ columns.flatMap u64Le

theorem append_port (out : GoSlice) (prior : List w8) (port : Vector)
    (selector : Option w64) (columns : List w64) (dq : DFrac) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗
        OptionalWord port.Selector' selector dq ∗ port.Columns' ↦*{dq} columns : IProp GF) }}
      (App (App (Val (@! appendWirePort)) (Val #out)) (Val #port))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ portBytes port selector columns) ∗ ownSliceCap w8 result (DFrac.own 1) ∗
        OptionalWord port.Selector' selector dq ∗ port.Columns' ↦*{dq} columns }} := by
  wp_start as ⟨Hout,Hcap,Hselector,Hcolumns⟩
  ihave %Hlen := ownSlice_len $$ Hcolumns
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply (append_option _ _ port.Selector' selector dq) $$ [Hout Hcap Hselector]
    with %next ⟨Hout,Hcap,Hselector⟩
  · iframe Hout Hcap Hselector
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  have Hword : port.Columns'.len = W64 columns.length := by word
  isimp only [Hword] at Hout
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : w64),
      "i" ∷ i_ptr ↦ n ∗ "out" ∷ out_ptr ↦ current ∗ "col" ∷ col_ptr ↦ last ∗
      "Hout" ∷ current ↦* (prior ++ u64Le port.Module' ++ optionBytes selector ++
        u64Le (W64 columns.length) ++ (columns.take (sint.nat n)).flatMap u64Le) ∗
      "Hcap" ∷ ownSliceCap w8 current (DFrac.own 1) ∗ "Hcolumns" ∷ port.Columns' ↦*{dq} columns ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z port.Columns'.len⌝)
      $$ [i out col Hout Hcap Hcolumns]
  · iexists (W64 0),next,(W64 0)
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero,List.flatMap_nil,List.append_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < columns.length := by word
    have Hvalue := List.getElem?_eq_getElem Hlt
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z port.Columns'.len from ⟨Hn.1,Hif⟩,
      _root_.and_self,ite_true]
    wp_apply wp_load_slice_index port.Columns' (sint.Z n) columns dq columns[sint.nat n] Hn.1
      $$ [Hcolumns] with Hcolumns
    · iframe Hcolumns; ipureintro; exact Hvalue
    wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_for_post
    iframe
    iexists (n + W64 1),result,columns[sint.nat n]
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hstep,List.take_add_one,Hvalue]
    simp only [Option.toList_some,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = columns.length := by word
    isimp only [Heq,List.take_length] at Hout
    iapply HΦ
    simp only [portBytes,List.append_assoc]
    iframe Hout Hcap Hselector Hcolumns

#print axioms append_port
end
end divremfv.internal.airdata.SourceCapture
end Perennial
