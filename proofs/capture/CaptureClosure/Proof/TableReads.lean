module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.schema

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.schema

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Table.TypeAssumptions]
variable (F C : go.GoType) {F' C' : Type}
variable [ZeroVal F'] [TypeRepr F F'] [ZeroVal C'] [TypeRepr C C']

/-- The actual source getter returns the original constraint slice descriptor. -/
theorem Table.rawConstraints_correct (p : Loc) (v : GoSlice) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Table F' C', go!"constraints"] ↦{dq} v : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType (Table.ty F C) @!! go!"RawConstraints")) (Val #()))
    {{ RET #v; p.[Table F' C', go!"constraints"] ↦{dq} v }} := by
  wp_start as Hfield
  wp_auto
  iapply HΦ $$ Hfield

/-- The actual source getter returns the original register slice descriptor. -/
theorem Table.registers_correct (p : Loc) (v : GoSlice) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Table F' C', go!"registers"] ↦{dq} v : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType (Table.ty F C) @!! go!"Registers")) (Val #()))
    {{ RET #v; p.[Table F' C', go!"registers"] ↦{dq} v }} := by
  wp_start as Hfield
  wp_auto
  iapply HΦ $$ Hfield

/-- Static activation is read from the actual table flag. -/
theorem Table.isStatic_correct (p : Loc) (v : Bool) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Table F' C', go!"static"] ↦{dq} v : IProp GF) }}
      (App (Val (p @!! go.GoType.PointerType (Table.ty F C) @!! go!"IsStatic")) (Val #()))
    {{ RET #v; p.[Table F' C', go!"static"] ↦{dq} v }} := by
  wp_start as Hfield
  wp_auto
  iapply HΦ $$ Hfield

theorem Table.name_correct (p : Loc) (name : GoString) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Table F' C', go!"name"] ↦{dq} name : IProp GF) }}
      (App (Val (p @!! go.PointerType (Table.ty F C) @!! go!"Name")) (Val #()))
    {{ RET #name; p.[Table F' C', go!"name"] ↦{dq} name }} := by
  wp_start as Hfield
  wp_auto
  iapply HΦ $$ Hfield

theorem Table.isNative_correct (p : Loc) (flag : Bool) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Table F' C', go!"native"] ↦{dq} flag : IProp GF) }}
      (App (Val (p @!! go.PointerType (Table.ty F C) @!! go!"IsNative")) (Val #()))
    {{ RET #flag; p.[Table F' C', go!"native"] ↦{dq} flag }} := by
  wp_start as Hfield
  wp_auto
  iapply HΦ $$ Hfield

theorem Table.staticContents_correct (p : Loc) (content : GoSlice) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Table F' C', go!"static"] ↦{dq} true ∗
        p.[Table F' C', go!"staticContents"] ↦{dq} content : IProp GF) }}
      (App (Val (p @!! go.PointerType (Table.ty F C) @!! go!"StaticContents")) (Val #()))
    {{ RET #content; p.[Table F' C', go!"static"] ↦{dq} true ∗
        p.[Table F' C', go!"staticContents"] ↦{dq} content }} := by
  wp_start as ⟨Hstatic,Hcontent⟩
  wp_auto
  iapply HΦ
  iframe Hstatic Hcontent

#print axioms Table.name_correct
#print axioms Table.isNative_correct
#print axioms Table.staticContents_correct
#print axioms Table.rawConstraints_correct
#print axioms Table.registers_correct
#print axioms Table.isStatic_correct
end
end github_com.LFDT_Lineth.zkc.pkg.schema
end Perennial
