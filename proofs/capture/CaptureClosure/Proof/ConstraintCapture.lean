module
public import CaptureClosure.Proof.LookupPortsCapture
public import CaptureClosure.Proof.BusPortsCapture
public import CaptureClosure.Proof.DomainCapture
public import CaptureClosure.Proof.ConstraintReads
public import CaptureClosure.Proof.ConstraintWire
public import CaptureClosure.Proof.RecursiveCapture

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
local notation "FType" => github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.ty
local notation "LogicalType" => github_com.LFDT_Lineth.zkc.pkg.ir.air.LogicalTerm.ty FType
local notation "Logical" => github_com.LFDT_Lineth.zkc.pkg.ir.air.LogicalTerm (GoArray w32 1)
local notation "Vanish" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing.Constraint
local notation "Ranged" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged.Constraint
local notation "Lookup" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Constraint
local notation "Bus" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Constraint
local notation "LookupVector" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector
local notation "BusPort" => github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port
local notation "Option64" => github_com.LFDT_Lineth.zkc.pkg.util.Option w64
open github_com.LFDT_Lineth.zkc.pkg.trace

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

def InputRule (mid : w64) (name : GoString) (model : DivRemFV.CaptureSyntax.Rule) (source : GoInterface) : IProp GF :=
  match model with
  | .vanishing owner domain term => iprop(∃ (p : Loc) (rawDomain : Option64) (expression : GoInterface),
      ⌜source = interface.mkOk (go.PointerType (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing.Constraint.ty FType LogicalType)) #p ∧ p ≠ null ∧
        owner = mid.toNat ∧ domain = (domainValue rawDomain).map sint.Z⌝ ∗
      p.[Vanish (GoArray w32 1) Logical,go!"Handle"] ↦□ name ∗
      p.[Vanish (GoArray w32 1) Logical,go!"Context"] ↦□ mid ∗
      p.[Vanish (GoArray w32 1) Logical,go!"Domain"] ↦□ rawDomain ∗
      p.[Vanish (GoArray w32 1) Logical,go!"Constraint"].[Logical,go!"Term"] ↦□ expression ∗ InputTerm term expression)
  | .range owner column bits => iprop(∃ (p : Loc) (index width : w64),
      ⌜source = interface.mkOk (go.PointerType (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged.Constraint.ty FType)) #p ∧ p ≠ null ∧
        owner = mid.toNat ∧ column = index.toNat ∧ bits = width.toNat ∧ index ≠ W64 (2^64-1)⌝ ∗
      p.[Ranged (GoArray w32 1),go!"Handle"] ↦□ name ∗
      p.[Ranged (GoArray w32 1),go!"Context"] ↦□ mid ∗
      p.[Ranged (GoArray w32 1),go!"Source"] ↦□ ColumnId.mk index ∗
      p.[Ranged (GoArray w32 1),go!"Bitwidth"] ↦□ width)
  | .lookup sources targets => iprop(∃ (p : Loc) (sourceSlice targetSlice : GoSlice)
      (sourceValues targetValues : List LookupVector),
      ⌜source = interface.mkOk (go.PointerType (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Constraint.ty FType)) #p ∧ p ≠ null⌝ ∗
      p.[Lookup (GoArray w32 1),go!"Handle"] ↦□ name ∗
      p.[Lookup (GoArray w32 1),go!"Sources"] ↦□ sourceSlice ∗ sourceSlice ↦*□ sourceValues ∗ InputLookupPorts sources sourceValues ∗
      p.[Lookup (GoArray w32 1),go!"Targets"] ↦□ targetSlice ∗ targetSlice ↦*□ targetValues ∗ InputLookupPorts targets targetValues)
  | .bus sources targets => iprop(∃ (p : Loc) (sourceSlice targetSlice : GoSlice)
      (sourceValues targetValues : List BusPort),
      ⌜source = interface.mkOk (go.PointerType (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Constraint.ty FType)) #p ∧ p ≠ null⌝ ∗
      p.[Bus (GoArray w32 1),go!"Handle"] ↦□ name ∗
      p.[Bus (GoArray w32 1),go!"Sends"] ↦□ sourceSlice ∗ sourceSlice ↦*□ sourceValues ∗ InputBusPorts sources sourceValues ∗
      p.[Bus (GoArray w32 1),go!"Receives"] ↦□ targetSlice ∗ targetSlice ↦*□ targetValues ∗ InputBusPorts targets targetValues)

instance (mid : w64) (name : GoString) (model : DivRemFV.CaptureSyntax.Rule) (source : GoInterface) :
    Persistent (InputRule (GF := GF) mid name model source) := by
  cases model <;> simp only [InputRule] <;> infer_instance

def InputEntry (mid id : w64) (model : DivRemFV.CaptureSyntax.Entry) (source : GoInterface) : IProp GF :=
  iprop(∃ name : GoString, ⌜model.id = id.toNat ∧ model.owner = mid.toNat ∧
    model.name = name.map BitVec.toNat ∧ name.length < 2^63⌝ ∗ InputRule mid name model.rule source)

instance (mid id : w64) (model : DivRemFV.CaptureSyntax.Entry) (source : GoInterface) :
    Persistent (InputEntry (GF := GF) mid id model source) := by unfold InputEntry; infer_instance

variable [Constraint.TypeAssumptions] [Term.TypeAssumptions] [Vector.TypeAssumptions] [ColumnId.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.Option.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear.Element.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.Term.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.air.LogicalTerm.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Constant.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.RegisterAccess.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Add.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Sub.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.ir.term.Mul.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Constraint.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Vector.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Port.TypeAssumptions]
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

theorem capture_entry (mid id : w64) (model : DivRemFV.CaptureSyntax.Entry) (source : GoInterface) :
    {{ (InputEntry mid id model source : IProp GF) }}
      (App (App (App (Val (@! exportConstraint)) (Val #mid)) (Val #id)) (Val #source))
    {{ (result : Constraint), RET (PairV #result #interface.nil); EntryValue model result (DFrac.own 1) }} := by
  wp_start as #Hinput
  iunfold InputEntry at Hinput
  icases Hinput with ⟨%name,⟨%Hid,%Howner,%Hname,%Hlen⟩,#Hrule⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Vector.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Vector) (t := Vector.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %emptySources ⟨HemptySources,HsourceCap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType Vector.ty)))) (Val (LiteralValueV [])))
  iapply wp_slice_literal (V := Vector) (t := Vector.ty) []
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %emptyTargets ⟨HemptyTargets,HtargetCap⟩
  wp_auto
  cases Hcase : model.rule with
  | vanishing owner domain term =>
    isimp only [Hcase,InputRule] at Hrule
    icases Hrule with ⟨%p,%rawDomain,%expression,⟨%Hsource,%Hnonnull,%Hown,%Hdomain⟩,
      #Hhandle,#Hcontext,#HdomainField,#HtermField,#Hterm⟩
    subst source
    wp_auto
    wp_apply (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing.Constraint.name_correct
      FType LogicalType p name DFrac.discard Hnonnull) with _
    · iframe Hhandle
    wp_apply (capture_domain rawDomain) with %domainPointer HdomainValue
    all_goals try itrivial
    wp_apply (capture_term term expression) with %result Hresult
    · iframe Hterm
    try wp_auto
    ihave ⟨expr,%HexprNonNull⟩ := typedPointsto_not_null_dup expr_ptr result (DFrac.own 1) $$ expr
    iapply HΦ
    isimp only [EntryValue,Hcase,RuleValue]
    isplitl []
    · ipureintro; exact ⟨Hid,Howner,Hname,Hlen⟩
    iexists domainValue rawDomain,result
    iframe HdomainValue expr Hresult
    ipureintro; exact ⟨True.intro,Hown,Hdomain,HexprNonNull⟩
  | range owner column bits =>
    isimp only [Hcase,InputRule] at Hrule
    icases Hrule with ⟨%p,%index,%width,⟨%Hsource,%Hnonnull,%Hown,%Hcolumn,%Hbits,%Hvalid⟩,
      #Hhandle,#Hcontext,#Hindex,#Hwidth⟩
    subst source
    wp_auto
    wp_apply (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged.Constraint.name_correct
      FType p name DFrac.discard Hnonnull) with _
    · iframe Hhandle
    wp_apply (ColumnId.unwrap_correct index Hvalid)
    all_goals try itrivial
    try wp_auto
    iapply HΦ
    isimp only [EntryValue,Hcase,RuleValue]
    ipureintro; exact ⟨⟨Hid,Howner,Hname,Hlen⟩,True.intro,Hown,Hcolumn,Hbits⟩
  | lookup sources targets =>
    isimp only [Hcase,InputRule] at Hrule
    icases Hrule with ⟨%p,%sourceSlice,%targetSlice,%sourceValues,%targetValues,⟨%Hsource,%Hnonnull⟩,
      #Hhandle,#HsourceField,#HsourceSlice,#HsourceModels,#HtargetField,#HtargetSlice,#HtargetModels⟩
    subst source
    wp_auto
    wp_apply (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup.Constraint.name_correct
      FType p name DFrac.discard Hnonnull) with _
    · iframe Hhandle
    wp_apply (capture_lookup_ports sourceSlice sources sourceValues DFrac.discard)
      with %sourceResult ⟨%sourceOutputs,Hsources,HsourceCap,HsourceModels,_,_⟩
    · iframe HsourceSlice HsourceModels
    wp_apply (capture_lookup_ports targetSlice targets targetValues DFrac.discard)
      with %targetResult ⟨%targetOutputs,Htargets,HtargetCap,HtargetModels,_,_⟩
    · iframe HtargetSlice HtargetModels
    iapply HΦ
    isimp only [EntryValue,Hcase,RuleValue]
    isplitl []
    · ipureintro; exact ⟨Hid,Howner,Hname,Hlen⟩
    iexists sourceOutputs,targetOutputs
    iframe Hsources HsourceModels Htargets HtargetModels
  | bus sources targets =>
    isimp only [Hcase,InputRule] at Hrule
    icases Hrule with ⟨%p,%sourceSlice,%targetSlice,%sourceValues,%targetValues,⟨%Hsource,%Hnonnull⟩,
      #Hhandle,#HsourceField,#HsourceSlice,#HsourceModels,#HtargetField,#HtargetSlice,#HtargetModels⟩
    subst source
    wp_auto
    wp_apply (github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus.Constraint.name_correct
      FType p name DFrac.discard Hnonnull) with _
    · iframe Hhandle
    wp_apply (capture_bus_ports sourceSlice sources sourceValues DFrac.discard)
      with %sourceResult ⟨%sourceOutputs,Hsources,HsourceCap,HsourceModels,_,_⟩
    · iframe HsourceSlice HsourceModels
    wp_apply (capture_bus_ports targetSlice targets targetValues DFrac.discard)
      with %targetResult ⟨%targetOutputs,Htargets,HtargetCap,HtargetModels,_,_⟩
    · iframe HtargetSlice HtargetModels
    iapply HΦ
    isimp only [EntryValue,Hcase,RuleValue]
    isplitl []
    · ipureintro; exact ⟨Hid,Howner,Hname,Hlen⟩
    iexists sourceOutputs,targetOutputs
    iframe Hsources HsourceModels Htargets HtargetModels

#print axioms capture_entry
end
end divremfv.internal.airdata.SourceCapture
end Perennial

