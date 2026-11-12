module
public import CaptureClosure.Proof.EncodeTerm

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

theorem wireBytes_length (words : List Nat) : (wireBytes words).length = words.length * 8 := by
  induction words with
  | nil => rfl
  | cons head tail ih =>
    simp only [wireBytes_cons,List.length_append,ih,List.length_cons,little_endian_bytes,List.length_nil]
    omega

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Term.TypeAssumptions]
variable [FuncUnfold appendWireFramedTerm [] appendWireFramedTerm.impl]
variable [FuncUnfold EncodeTermWire [] EncodeTermWire.impl]
variable [FuncUnfold appendTermWire [] appendTermWire.impl]
variable [FuncUnfold appendArgsWire [] appendArgsWire.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

theorem serialize_framed_term (out : GoSlice) (prior : List w8) (model : ModelTerm) (value : Term) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OutputTerm model value : IProp GF) }}
      (App (App (Val (@! appendWireFramedTerm)) (Val #out)) (Val #value))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* (prior ++ wireBytes (DivRemFV.CaptureSyntax.natWords model.words)) ∗
      ownSliceCap w8 result (DFrac.own 1) ∗ OutputTerm model value }} := by
  wp_start as ⟨Hout,Hcap,Hmodel⟩
  wp_auto
  wp_apply (encode_term model value) $$ [Hmodel] with %encoded ⟨Hencoded,HencodedCap,Hmodel⟩
  · iframe Hmodel
  ihave %Hlen := ownSlice_len $$ Hencoded
  rw [wireBytes_length] at Hlen
  have Hword : BitVec.sdiv encoded.len (W64 8) = W64 model.words.length := by word
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply wp_slice_append (V := w8) (st := go.SliceType go.byte) (t := go.byte)
    next _ encoded (wireBytes model.words) (DFrac.own 1)
    $$ [Hout Hcap Hencoded] with %result ⟨Hout,Hcap,Hencoded⟩
  · iframe Hout Hcap Hencoded
  iapply HΦ
  simp only [DivRemFV.CaptureSyntax.natWords,wireBytes_cons,List.append_assoc]
  try isimp only [Hword,List.append_assoc] at Hout
  iframe Hout Hcap Hmodel

#print axioms serialize_framed_term
end
end divremfv.internal.airdata.SourceCapture
end Perennial
