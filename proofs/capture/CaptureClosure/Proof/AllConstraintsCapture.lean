module
public import CaptureClosure.Proof.ConstraintsCapture
public import CaptureClosure.Proof.TableReads

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
local notation "FType" => github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty
local notation "CType" => github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.ty FType
local notation "SourceTable" => github_com.LFDT_Lineth.zkc.pkg.schema.Table (GoArray w32 1) GoInterface
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

def InputTableEntries (mid first : w64) (models : List DivRemFV.CaptureSyntax.Entry) (p : Loc) : IProp GF :=
  iprop(∃ (sl : GoSlice) (values : List GoInterface), ⌜p ≠ null⌝ ∗
    p.[SourceTable,go!"constraints"] ↦□ sl ∗ sl ↦*□ values ∗ InputEntries mid first models values)
instance (mid first : w64) (models : List DivRemFV.CaptureSyntax.Entry) (p : Loc) :
    Persistent (InputTableEntries (GF := GF) mid first models p) := by unfold InputTableEntries; infer_instance

abbrev InputAllEntries (models : List (List DivRemFV.CaptureSyntax.Entry)) (values : List Loc) : IProp GF :=
  iprop([∗list] k ↦ entries;source ∈ models;values,
    InputTableEntries (W64 k) (W64 ((models.take k).flatten.length)) entries source)

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
variable [github_com.LFDT_Lineth.zkc.pkg.schema.Table.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.TypeAssumptions]
variable [FuncUnfold exportAllConstraints [] exportAllConstraints.impl]
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

theorem capture_all_constraints (sl : GoSlice) (models : List (List DivRemFV.CaptureSyntax.Entry)) (sources : List Loc) :
    {{ (sl ↦*□ sources ∗ InputAllEntries models sources : IProp GF) }}
      (App (Val (@! exportAllConstraints)) (Val #sl))
    {{ (result : GoSlice), RET (PairV #result #interface.nil); ∃ values : List Constraint,
      result ↦* values ∗ ownSliceCap Constraint result (DFrac.own 1) ∗ ConstraintsValue models.flatten values (DFrac.own 1) }} := by
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
  ihave IH : iprop(∃ (n : w64) (current : GoSlice) (last : Loc) (values : List Constraint) (key : w64),
      "i" ∷ i_ptr ↦ n ∗ "mid" ∷ mid_ptr ↦ key ∗ "out" ∷ out_ptr ↦ current ∗ "m" ∷ m_ptr ↦ last ∗
      "Hout" ∷ current ↦* values ∗ "Hcap" ∷ ownSliceCap Constraint current (DFrac.own 1) ∗
      "Hmodels" ∷ ConstraintsValue (models.take (sint.nat n)).flatten values (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝) $$ [i mid out m Hout Hcap]
  · iexists (W64 0),_,null,[],(W64 0)
    simp only [show sint.nat (W64 0) = 0 from rfl,List.take_zero,List.flatten_nil]
    iframe
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < sources.length := by word
    have Hmlt : sint.nat n < models.length := by word
    have Hlookup := List.getElem?_eq_getElem Hlt
    let selected := models[sint.nat n]
    let table := sources[sint.nat n]
    have Hmodel := List.getElem?_eq_getElem Hmlt
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1,Hif⟩,_root_.and_self,ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) sources DFrac.discard table Hn.1 with _
    · iframe Hsource; ipureintro; exact Hlookup
    ihave #Hchild := BigSepL2.bigSepL2_lookup Hmodel Hlookup $$ Hinputs
    isimp only [InputTableEntries] at Hchild
    icases Hchild with ⟨%constraints,%constraintSources,%Hnonnull,#Hfield,#HconstraintSources,#HconstraintInputs⟩
    ihave %HcurrentLen := ownSlice_len $$ Hout
    ihave %HprefixLen := BigSepL2.bigSepL2_length $$ Hmodels
    have Hcast : W64 (sint.nat n) = n := by word
    have Hfirst : W64 ((models.take (sint.nat n)).flatten.length) = current.len := by word
    try isimp only [Hcast,Hfirst] at HconstraintInputs
    wp_apply (github_com.LFDT_Lineth.zkc.pkg.schema.Table.rawConstraints_correct
      FType CType table constraints DFrac.discard Hnonnull) with _
    · iframe Hfield
    wp_apply (capture_constraints n current.len constraints selected constraintSources)
      with %child ⟨%childValues,Hchild,HchildCap,HchildModels⟩
    · iframe HconstraintSources HconstraintInputs
    ihave %HchildLen := BigSepL2.bigSepL2_length $$ HchildModels
    wp_apply wp_slice_append (V := Constraint) (st := go.SliceType Constraint.ty) (t := Constraint.ty)
      current values child childValues (DFrac.own 1) $$ [Hout Hcap Hchild]
      with %result ⟨Hout,Hcap,Hchild⟩
    · iframe Hout Hcap Hchild
    wp_for_post
    iframe
    iexists (n + W64 1),result,table,(values ++ childValues),n
    have Hstep : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hprefix : (models.take (sint.nat (n + W64 1))).flatten =
        (models.take (sint.nat n)).flatten ++ selected := by
      rw [Hstep,List.take_add_one,Hmodel]
      simp only [Option.toList_some,List.flatten_append,List.flatten_cons,List.flatten_nil,List.append_nil]
      rfl
    ihave Hnext : ConstraintsValue ((models.take (sint.nat n)).flatten ++ selected)
        (values ++ childValues) (DFrac.own 1) $$ [Hmodels HchildModels]
    · iapply (BigSepL2.bigSepL2_append (Or.inr HchildLen)).2
      iframe Hmodels HchildModels
    rw [Hprefix]
    iframe
    ipureintro; constructor <;> word
  · have Htest := Hif
    try simp only [decide_eq_false Htest,Bool.false_eq_true,ite_false]
    have Heq : sint.nat n = models.length := by word
    isimp only [Heq,List.take_length] at Hmodels
    iapply HΦ
    iexists values
    iframe Hout Hcap Hmodels

#print axioms capture_all_constraints
end
end divremfv.internal.airdata.SourceCapture
end Perennial

