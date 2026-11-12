module
public import CaptureClosure.Proof.ColumnModel
public import CaptureClosure.Proof.RawRegisterReads

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

local notation "Reg" => github_com.LFDT_Lineth.zkc.pkg.schema.register.Register
local notation "Kind" => github_com.LFDT_Lineth.zkc.pkg.schema.register.Type'
local notation "RegType" => github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.ty
open github_com.LFDT_Lineth.zkc.pkg.schema.register

def registerColumn [FfiSyntax] (id : w64) (value : Reg) (inputTag outputTag : Kind) :
    DivRemFV.CaptureSyntax.Column :=
  ⟨id.toNat,value.name'.map BitVec.toNat,
    if value.width' = W64 (2^64-1) then none else some value.width'.toNat,
    decide (value.kind'.kind' = inputTag.kind'),decide (value.kind'.kind' = outputTag.kind'),
    decide (value.width' = W64 (2^64-1))⟩

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Column.TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.register.«Type».TypeAssumptions]
variable [github_com.LFDT_Lineth.zkc.pkg.schema.register.Register.TypeAssumptions]
variable [FuncUnfold exportColumn [] exportColumn.impl]

theorem capture_column (id : w64) (value : Reg) (inputTag outputTag : Kind)
    (bounded : value.name'.length < 2^63) :
    {{ (globalAddr INPUT_REGISTER ↦□ inputTag ∗ globalAddr OUTPUT_REGISTER ↦□ outputTag : IProp GF) }}
      (App (App (Val (@! exportColumn)) (Val #id)) (Val #value))
    {{ (result : Column), RET #result; ColumnValue (registerColumn id value inputTag outputTag) result (DFrac.own 1) }} := by
  wp_start as ⟨#Hinput,#Houtput⟩
  wp_auto
  wp_apply Register.name_correct
  all_goals try itrivial
  try wp_auto
  ihave ⟨r,%Hp⟩ := typedPointsto_not_null_dup r_ptr value (DFrac.own 1) $$ r
  wp_apply (Register.input_record r_ptr value inputTag (DFrac.own 1) Hp)
    $$ [r] with ⟨r,_⟩
  · iframe r Hinput
  wp_apply (Register.output_record r_ptr value outputTag (DFrac.own 1) Hp)
    $$ [r] with ⟨r,_⟩
  · iframe r Houtput
  wp_apply (Register.native_record r_ptr value (DFrac.own 1) Hp) $$ [r] with r
  · iframe r
  wp_apply (Register.native_record r_ptr value (DFrac.own 1) Hp) $$ [r] with r
  · iframe r
  by_cases native : value.width' = W64 (2^64-1)
  · rw [decide_eq_true native]
    wp_auto
    iapply HΦ
    isimp only [ColumnValue]
    iexists none
    isplitl []
    · ipureintro
      constructor
      · simp [registerColumn,portableColumn,native]
      · exact bounded
    isimp only [OptionalWord]
    ipureintro; trivial
  · rw [decide_eq_false native]
    wp_auto
    wp_apply (Register.width_correct value native)
    all_goals try itrivial
    try wp_auto
    ihave ⟨width,%Hwidth⟩ := typedPointsto_not_null_dup width_ptr value.width' (DFrac.own 1) $$ width
    iapply HΦ
    isimp only [ColumnValue]
    iexists (some value.width')
    isimp only [OptionalWord]
    isplitl []
    · ipureintro
      constructor
      · simp [registerColumn,portableColumn,native]
        word
      · exact bounded
    isplitl []
    · ipureintro; exact Hwidth
    iexact width

#print axioms capture_column
end
end divremfv.internal.airdata.SourceCapture
end Perennial
