module
public import CaptureClosure.Proof.ColumnWire
public import CaptureClosure.Proof.WireNumbers

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

def domainBytes : Option w64 → List w8
  | none => u64Le (W64 0) ++ u64Le (W64 0)
  | some value => u64Le (W64 1) ++ u64Le (zigzagWord value)

theorem domainBytes_words (value : Option w64) :
    domainBytes value = wireBytes (DivRemFV.CaptureSyntax.optionIntWords (value.map sint.Z)) := by
  cases value with
  | none => rfl
  | some value =>
    simp only [domainBytes,DivRemFV.CaptureSyntax.optionIntWords,Option.map_some,
      wireBytes_cons,wireBytes_nil,List.append_nil]
    rw [← zigzag_word_value]
    congr 2
    word

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [FuncUnfold appendWireDomain [] appendWireDomain.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

theorem serialize_domain (out : GoSlice) (prior : List w8) (p : Loc) (value : Option w64) (dq : DFrac) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ OptionalWord p value dq : IProp GF) }}
      (App (App (Val (@! appendWireDomain)) (Val #out)) (Val #p))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ domainBytes value) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ OptionalWord p value dq }} := by
  wp_start as ⟨Hout,Hcap,Hvalue⟩
  cases value with
  | none =>
    isimp only [OptionalWord] at Hvalue
    icases Hvalue with %Hp
    subst p
    wp_auto
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    iapply HΦ
    simp only [domainBytes,List.append_assoc]
    try isimp only [List.append_assoc] at Hout
    iframe Hout Hcap
    isimp only [OptionalWord]
    ipureintro; trivial
  | some value =>
    isimp only [OptionalWord] at Hvalue
    icases Hvalue with ⟨%Hp,Hpoint⟩
    wp_auto
    rw [decide_eq_false Hp]
    wp_auto
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    iapply HΦ
    simp only [domainBytes,zigzagWord,List.append_assoc]
    try isimp only [List.append_assoc] at Hout
    iframe Hout Hcap
    isimp only [OptionalWord]
    iframe Hpoint
    ipureintro; exact Hp

#print axioms serialize_domain
end
end divremfv.internal.airdata.SourceCapture
end Perennial
