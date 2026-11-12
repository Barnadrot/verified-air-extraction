module
public import CaptureClosure.Proof.TermModel
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
variable [sem : go.Semantics] [Term.TypeAssumptions]
variable [FuncUnfold appendTermWire [] appendTermWire.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

theorem append_constant (out : GoSlice) (prior : List w8)
    (value : DivRemFV.CaptureSyntax.FieldValue) (args : GoSlice) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ args ↦* ([] : List Term) : IProp GF) }}
      (App (App (Val (@! appendTermWire)) (Val #out))
        (Val #(Term.mk go!"constant" (W64 value.val) (W64 0) (W64 0) args)))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* (prior ++ u64Le (W64 0) ++ u64Le (W64 value.val)) ∗
      ownSliceCap w8 result (DFrac.own 1) ∗ args ↦* ([] : List Term) }} := by
  wp_start as ⟨Hout,Hcap,Hargs⟩
  ihave %Hlen := ownSlice_len $$ Hargs
  have Hvalue := value.isLt
  change value.val < 2130706433 at Hvalue
  wp_auto
  have Hbound : ¬ uint.Z (W64 value.val) ≥ uint.Z (W64 2130706433) := by word
  rw [decide_eq_false Hbound]
  wp_auto
  have Hzero : args.len = W64 0 := by simp only [List.length_nil] at Hlen; word
  rw [Hzero]
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  iapply HΦ
  iframe Hout Hcap Hargs

#print axioms append_constant

def zigzagWord (shift : w64) : w64 :=
  (shift <<< W64 1) ^^^ (BitVec.sshiftRight' shift (W64 63))

theorem append_column (out : GoSlice) (prior : List w8) (index shift : w64) (args : GoSlice) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ args ↦* ([] : List Term) : IProp GF) }}
      (App (App (Val (@! appendTermWire)) (Val #out))
        (Val #(Term.mk go!"column" (W64 0) index shift args)))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* (prior ++ u64Le (W64 1) ++ u64Le index ++ u64Le (zigzagWord shift)) ∗
      ownSliceCap w8 result (DFrac.own 1) ∗ args ↦* ([] : List Term) }} := by
  wp_start as ⟨Hout,Hcap,Hargs⟩
  ihave %Hlen := ownSlice_len $$ Hargs
  have Hzero : args.len = W64 0 := by simp only [List.length_nil] at Hlen; word
  wp_auto
  rw [Hzero]
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  iapply HΦ
  simp only [zigzagWord,show (1 : w64) = W64 1 by word,show (63 : w64) = W64 63 by word]
  iframe Hout Hcap Hargs

#print axioms append_column
end
end divremfv.internal.airdata.SourceCapture
end Perennial
