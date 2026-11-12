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
variable [sem : go.Semantics] [UniformSchema.TypeAssumptions]
variable (F M : go.GoType) {F' M' : Type}
variable [ZeroVal F'] [TypeRepr F F'] [ZeroVal M'] [TypeRepr M M']

instance : TypedPointsto (GF := GF) (UniformSchema F' M') where
  typedPointstoDef l v dq := iprop(
    "modules" ∷ typedPointsto (structFieldRef (UniformSchema F' M') go!"modules" l) v.modules' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

instance : IntoValTypedUnderlying (GF := GF) (UniformSchema F' M') (UniformSchema.underlying F M) := by
  solve_into_val_typed_struct

instance (l : Loc) (v : UniformSchema F' M') (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef (UniformSchema F' M') go!"modules" l) v.modules' dq)
      (typedPointsto (structFieldRef (UniformSchema F' M') go!"modules" l) v.modules' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) := by
  solve_pointsto_access_struct

/-- The actual source method returns the original module slice descriptor. -/
theorem UniformSchema.rawModules_correct (v : UniformSchema F' M') :
    {{ (True : IProp GF) }}
      (App (Val (v @!! UniformSchema.ty F M @!! go!"RawModules")) (Val #()))
    {{ RET #(v.modules'); True }} := by
  wp_start
  wp_auto
  wp_end

#print axioms UniformSchema.rawModules_correct
end
end github_com.LFDT_Lineth.zkc.pkg.schema
end Perennial
