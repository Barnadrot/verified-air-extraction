module
public import CaptureClosure.Proof.PortsWire
public import CaptureClosure.Proof.DomainWire
public import CaptureClosure.Proof.FramedTerm

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

def RuleValue (model : DivRemFV.CaptureSyntax.Rule) (value : Constraint) (dq : DFrac) : IProp GF :=
  match model with
  | .vanishing owner domain term => iprop(∃ (rawDomain : Option w64) (expression : Term),
      ⌜value.Kind' = go!"vanishing" ∧ owner = value.Owner'.toNat ∧ domain = rawDomain.map sint.Z ∧ value.Expr' ≠ null⌝ ∗
      OptionalWord value.Domain' rawDomain dq ∗ value.Expr' ↦{dq} expression ∗ OutputTerm term expression)
  | .range owner column bits => iprop(⌜value.Kind' = go!"range" ∧ owner = value.Owner'.toNat ∧
      column = value.Column'.toNat ∧ bits = value.Bits'.toNat⌝)
  | .lookup sources targets => iprop(∃ (sourceValues targetValues : List Vector),
      ⌜value.Kind' = go!"lookup"⌝ ∗
      value.Sources' ↦*{dq} sourceValues ∗ PortsValue sources sourceValues dq ∗
      value.Targets' ↦*{dq} targetValues ∗ PortsValue targets targetValues dq)
  | .bus sources targets => iprop(∃ (sourceValues targetValues : List Vector),
      ⌜value.Kind' = go!"bus"⌝ ∗
      value.Sources' ↦*{dq} sourceValues ∗ PortsValue sources sourceValues dq ∗
      value.Targets' ↦*{dq} targetValues ∗ PortsValue targets targetValues dq)

def EntryValue (model : DivRemFV.CaptureSyntax.Entry) (value : Constraint) (dq : DFrac) : IProp GF :=
  iprop(⌜model.id = value.ID'.toNat ∧ model.owner = value.Owner'.toNat ∧
    model.name = value.Name'.map BitVec.toNat ∧ value.Name'.length < 2^63⌝ ∗ RuleValue model.rule value dq)

variable [Constraint.TypeAssumptions] [Term.TypeAssumptions] [Vector.TypeAssumptions]
variable [FuncUnfold appendWireConstraint [] appendWireConstraint.impl]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]
variable [FuncUnfold appendWireName [] appendWireName.impl]
variable [FuncUnfold appendWireOption [] appendWireOption.impl]
variable [FuncUnfold appendWireDomain [] appendWireDomain.impl]
variable [FuncUnfold appendWireFramedTerm [] appendWireFramedTerm.impl]
variable [FuncUnfold EncodeTermWire [] EncodeTermWire.impl]
variable [FuncUnfold appendTermWire [] appendTermWire.impl]
variable [FuncUnfold appendArgsWire [] appendArgsWire.impl]
variable [FuncUnfold appendWirePorts [] appendWirePorts.impl]
variable [FuncUnfold appendWirePort [] appendWirePort.impl]

theorem serialize_entry (out : GoSlice) (prior : List w8)
    (model : DivRemFV.CaptureSyntax.Entry) (value : Constraint) (dq : DFrac) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) ∗ EntryValue model value dq : IProp GF) }}
      (App (App (Val (@! appendWireConstraint)) (Val #out)) (Val #value))
    {{ (result : GoSlice), RET (PairV #result #interface.nil);
      result ↦* (prior ++ wireBytes model.words) ∗ ownSliceCap w8 result (DFrac.own 1) ∗ EntryValue model value dq }} := by
  wp_start as ⟨Hout,Hcap,Hmodel⟩
  isimp only [EntryValue] at Hmodel
  icases Hmodel with ⟨⟨%Hid,%Howner,%Hname,%Hlen⟩,Hrule⟩
  wp_auto
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  wp_apply (append_name _ _ value.Name' Hlen) $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
  · iframe Hout Hcap
  cases Hcase : model.rule with
  | vanishing owner domain term =>
    isimp only [Hcase,RuleValue] at Hrule
    icases Hrule with ⟨%rawDomain,%expression,⟨%Hkind,%Hown,%Hdomain,%Hnonnull⟩,HdomainValue,Hexpr,Hterm⟩
    rw [Hkind]
    wp_auto
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply (serialize_domain _ _ value.Domain' rawDomain dq)
      $$ [Hout Hcap HdomainValue] with %next ⟨Hout,Hcap,HdomainValue⟩
    · iframe Hout Hcap HdomainValue
    wp_apply (serialize_framed_term _ _ term expression)
      $$ [Hout Hcap Hterm] with %result ⟨Hout,Hcap,Hterm⟩
    · iframe Hout Hcap Hterm
    iapply HΦ
    simp only [DivRemFV.CaptureSyntax.Entry.words,Hid,Howner,Hname,Hcase,
      DivRemFV.CaptureSyntax.Rule.words,Hown,Hdomain,wireBytes_append,wireBytes_cons,
      wireBytes_nil,nameBytes_words,domainBytes_words,List.append_nil,List.append_assoc]
    have Hword : W64 value.Owner'.toNat = value.Owner' := by word
    have HwordId : W64 value.ID'.toNat = value.ID' := by word
    rw [Hword,HwordId]
    try isimp only [List.append_assoc] at Hout
    iframe Hout Hcap
    isimp only [EntryValue,Hcase,RuleValue]
    isplitl []
    · ipureintro; exact ⟨Hid,Howner,Hname,Hlen⟩
    iexists rawDomain,expression
    iframe HdomainValue Hexpr Hterm
    ipureintro; exact ⟨Hkind,Hown,Hdomain,Hnonnull⟩
  | range owner column bits =>
    isimp only [Hcase,RuleValue] at Hrule
    icases Hrule with ⟨%Hkind,%Hown,%Hcolumn,%Hbits⟩
    rw [Hkind]
    wp_auto
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply append_word $$ [Hout Hcap] with %result ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    iapply HΦ
    simp only [DivRemFV.CaptureSyntax.Entry.words,Hid,Howner,Hname,Hcase,
      DivRemFV.CaptureSyntax.Rule.words,Hown,Hcolumn,Hbits,wireBytes_append,wireBytes_cons,
      wireBytes_nil,nameBytes_words,List.append_nil,List.append_assoc]
    have Hw (n : w64) : W64 n.toNat = n := by word
    simp only [Hw]
    try isimp only [List.append_assoc] at Hout
    iframe Hout Hcap
    isimp only [EntryValue,Hcase,RuleValue]
    ipureintro; exact ⟨⟨Hid,Howner,Hname,Hlen⟩,Hkind,Hown,Hcolumn,Hbits⟩
  | lookup sources targets | bus sources targets =>
    isimp only [Hcase,RuleValue] at Hrule
    icases Hrule with ⟨%sourceValues,%targetValues,%Hkind,Hsources,HsourceModels,Htargets,HtargetModels⟩
    rw [Hkind]
    wp_auto
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    rw [Hkind]
    wp_auto
    wp_apply append_word $$ [Hout Hcap] with %next ⟨Hout,Hcap⟩
    · iframe Hout Hcap
    wp_apply (serialize_ports _ _ value.Sources' sources sourceValues dq)
      $$ [Hout Hcap Hsources HsourceModels] with %next ⟨Hout,Hcap,Hsources,HsourceModels⟩
    · iframe Hout Hcap Hsources HsourceModels
    wp_apply (serialize_ports _ _ value.Targets' targets targetValues dq)
      $$ [Hout Hcap Htargets HtargetModels] with %result ⟨Hout,Hcap,Htargets,HtargetModels⟩
    · iframe Hout Hcap Htargets HtargetModels
    iapply HΦ
    simp only [DivRemFV.CaptureSyntax.Entry.words,Hid,Howner,Hname,Hcase,
      DivRemFV.CaptureSyntax.Rule.words,wireBytes_append,wireBytes_cons,
      wireBytes_nil,nameBytes_words,List.append_nil,List.append_assoc]
    have Hw (n : w64) : W64 n.toNat = n := by word
    simp only [Hw]
    try isimp only [List.append_assoc] at Hout
    iframe Hout Hcap
    isimp only [EntryValue,Hcase,RuleValue]
    isplitl []
    · ipureintro; exact ⟨Hid,Howner,Hname,Hlen⟩
    iexists sourceValues,targetValues
    iframe Hsources HsourceModels Htargets HtargetModels
    ipureintro; exact Hkind

#print axioms serialize_entry
end
end divremfv.internal.airdata.SourceCapture
end Perennial
