module
public import CaptureClosure.Proof.ConstraintCapture
public import CaptureClosure.Proof.ConstraintsWire

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

abbrev InputEntries (mid first : w64) (models : List DivRemFV.CaptureSyntax.Entry) (values : List GoInterface) : IProp GF :=
  iprop([∗list] k ↦ model;source ∈ models;values, InputEntry mid (first + W64 k) model source)

variable [Constraint.TypeAssumptions] [Term.TypeAssumptions] [Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.trace.ColumnId.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.LogicalTerm.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Add.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.TypeAssumptions]
variable [FuncUnfold exportModuleConstraints [] exportModuleConstraints.impl]
variable [FuncUnfold exportConstraint [] exportConstraint.impl]
variable [FuncUnfold exportDomain [] exportDomain.impl]
variable [FuncUnfold exportLookupVectors [] exportLookupVectors.impl]
variable [FuncUnfold exportBusPorts [] exportBusPorts.impl]
variable [FuncUnfold lookupVector [] lookupVector.impl]
variable [FuncUnfold busVector [] busVector.impl]
variable [FuncUnfold uintRef [] uintRef.impl]
variable [FuncUnfold exportColumnIDs [] exportColumnIDs.impl]
variable [FuncUnfold ExportTerm [] ExportTerm.impl]
variable [FuncUnfold github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce []
  github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.montgomeryReduce.impl]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]

theorem capture_constraints (mid first : w64) (sl : GoSlice) (models : List DivRemFV.CaptureSyntax.Entry)
    (sources : List GoInterface) :
    {{ (sl ↦*□ sources ∗ InputEntries mid first models sources : IProp GF) }}
      (App (App (App (Val (@! exportModuleConstraints)) (Val #mid)) (Val #first)) (Val #sl))
    {{ (result : GoSlice), RET (PairV #result #interface.nil); ∃ values : List Constraint,
      result ↦* values ∗ ownSliceCap Constraint result (DFrac.own 1) ∗ ConstraintsValue models values (DFrac.own 1) }} := by
  wp_start as ⟨#Hsource,#Hinputs⟩
  ihave %Hlen := ownSlice_len $$ Hsource
  ihave %HmodelLen := BigSepL2.bigSepL2_length $$ Hinputs
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Constraint.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Constraint) (t := Constraint.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %empty ⟨Hout,Hcap⟩
  wp_auto
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : GoInterface) (values : List Constraint) (key : w64),
      "i" ∷ i_ptr ↦ n ∗ "index" ∷ index_ptr ↦ key ∗ "out" ∷ out_ptr ↦ current ∗ "source" ∷ source_ptr ↦ last ∗
      "Hout" ∷ current ↦* values ∗ "Hcap" ∷ ownSliceCap Constraint current (DFrac.own 1) ∗
      "Hmodels" ∷ ConstraintsValue (models.take (sint.nat n)) values (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i index out source Hout Hcap]
  · iexists (W64 0),_,interface.nil,[],(W64 0)
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero]
    iframe
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < sources.length := by word
    have Hmlt : sint.nat n < models.length := by word
    have Hlookup := List.getElem?_eq_getElem Hlt
    have Hmodel := List.getElem?_eq_getElem Hmlt
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1,Hif⟩,_root_.and_self,ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) sources DFrac.discard sources[sint.nat n] Hn.1 with _
    · iframe Hsource; ipureintro; exact Hlookup
    ihave #Hchild := BigSepL2.bigSepL2_lookup Hmodel Hlookup $$ Hinputs
    have Hcast : W64 (sint.nat n) = n := by word
    try isimp only [Hcast] at Hchild
    wp_apply (capture_entry mid (first + n) models[sint.nat n] sources[sint.nat n]) with %value Hvalue
    · iframe Hchild
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Constraint.ty)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Constraint) (t := Constraint.ty) [value]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %item ⟨Hitem,HitemCap⟩
    wp_auto
    wp_apply wp_slice_append (V := Constraint) (st := go.SliceType Constraint.ty) (t := Constraint.ty)
      current values _ [value] (DFrac.own 1) $$ [Hout Hcap Hitem] with %result ⟨Hout,Hcap,Hitem⟩
    · iframe Hout Hcap Hitem
    wp_for_post
    iframe
    iexists (n + W64 1),result,sources[sint.nat n],(values ++ [value]),n
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    rw [Hstep,List.take_add_one,Hmodel]
    simp only [Option.toList_some]
    ihave Hnext : ConstraintsValue (models.take (sint.nat n) ++ [models[sint.nat n]])
        (values ++ [value]) (DFrac.own 1) $$ [Hmodels Hvalue]
    · iapply BigSepL2.bigSepL2_snoc.2; iframe Hmodels Hvalue
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = models.length := by word
    isimp only [Heq,List.take_length] at Hmodels
    iapply HΦ
    iexists values
    iframe Hout Hcap Hmodels

#print axioms capture_constraints
end
end divremfv.internal.airdata.SourceCapture
end Perennial
