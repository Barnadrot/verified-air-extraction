module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Constraint.TypeAssumptions]
variable (F : go.GoType) {F' : Type} [ZeroVal F'] [TypeRepr F F']
variable (T : go.GoType) {T' : Type} [ZeroVal T'] [TypeRepr T T']

theorem Constraint.name_correct (p : Loc) (name : GoString) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Constraint F' T',go!"Handle"] ↦{dq} name : IProp GF) }}
      (App (Val (p @!! go.PointerType (Constraint.ty F T) @!! go!"Name")) (Val #()))
    {{ RET #name; p.[Constraint F' T',go!"Handle"] ↦{dq} name }} := by
  wp_start as Hname
  wp_auto
  iapply HΦ $$ Hname

#print axioms Constraint.name_correct
end
end github_com.LFDT_Lineth.zkc.pkg.schema.constraint.vanishing

namespace github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Constraint.TypeAssumptions]
variable (F : go.GoType) {F' : Type} [ZeroVal F'] [TypeRepr F F']

theorem Constraint.name_correct (p : Loc) (name : GoString) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Constraint F',go!"Handle"] ↦{dq} name : IProp GF) }}
      (App (Val (p @!! go.PointerType (Constraint.ty F) @!! go!"Name")) (Val #()))
    {{ RET #name; p.[Constraint F',go!"Handle"] ↦{dq} name }} := by
  wp_start as Hname
  wp_auto
  iapply HΦ $$ Hname

#print axioms Constraint.name_correct
end
end github_com.LFDT_Lineth.zkc.pkg.schema.constraint.ranged

namespace github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Constraint.TypeAssumptions]
variable (F : go.GoType) {F' : Type} [ZeroVal F'] [TypeRepr F F']

theorem Constraint.name_correct (p : Loc) (name : GoString) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Constraint F',go!"Handle"] ↦{dq} name : IProp GF) }}
      (App (Val (p @!! go.PointerType (Constraint.ty F) @!! go!"Name")) (Val #()))
    {{ RET #name; p.[Constraint F',go!"Handle"] ↦{dq} name }} := by
  wp_start as Hname
  wp_auto
  iapply HΦ $$ Hname

#print axioms Constraint.name_correct
end
end github_com.LFDT_Lineth.zkc.pkg.schema.constraint.lookup

namespace github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus
section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Constraint.TypeAssumptions]
variable (F : go.GoType) {F' : Type} [ZeroVal F'] [TypeRepr F F']

theorem Constraint.name_correct (p : Loc) (name : GoString) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Constraint F',go!"Handle"] ↦{dq} name : IProp GF) }}
      (App (Val (p @!! go.PointerType (Constraint.ty F) @!! go!"Name")) (Val #()))
    {{ RET #name; p.[Constraint F',go!"Handle"] ↦{dq} name }} := by
  wp_start as Hname
  wp_auto
  iapply HΦ $$ Hname

#print axioms Constraint.name_correct
end
end github_com.LFDT_Lineth.zkc.pkg.schema.constraint.bus
end Perennial
