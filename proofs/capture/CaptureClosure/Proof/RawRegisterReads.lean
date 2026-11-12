module
public import CaptureClosure.Proof.RegisterLayouts

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.schema.register

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [«Type».TypeAssumptions] [Register.TypeAssumptions]

theorem Register.name_correct (value : Register) :
    {{ (True : IProp GF) }}
      (App (Val (value @!! Register.ty @!! go!"Name")) (Val #()))
    {{ RET #value.name'; True }} := by
  wp_start as _
  wp_auto
  iapply HΦ
  itrivial

theorem Register.isNative_correct (p : Loc) (width : w64) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Register,go!"width"] ↦{dq} width : IProp GF) }}
      (App (Val (p @!! go.PointerType Register.ty @!! go!"IsNative")) (Val #()))
    {{ RET #(decide (width = W64 (2^64-1))); p.[Register,go!"width"] ↦{dq} width }} := by
  wp_start as Hwidth
  wp_auto
  rw [show W64 (2^64-1) = W64 18446744073709551615 from rfl]
  iapply HΦ $$ Hwidth

theorem Register.width_correct (value : Register) (notNative : value.width' ≠ W64 (2^64-1)) :
    {{ (True : IProp GF) }}
      (App (Val (value @!! Register.ty @!! go!"Width")) (Val #()))
    {{ RET #value.width'; True }} := by
  wp_start as _
  wp_auto
  ihave ⟨p,%Hp⟩ := typedPointsto_not_null_dup p_ptr value (DFrac.own 1) $$ p
  iStructNamed p
  wp_apply (Register.isNative_correct _ value.width' (DFrac.own 1) Hp) $$ [width] with Hwidth
  · iframe width
  rw [decide_eq_false notNative]
  wp_auto
  iapply HΦ
  itrivial

theorem Register.isInput_correct (p : Loc) (kind globalKind : Type') (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Register,go!"kind"] ↦{dq} kind ∗ globalAddr INPUT_REGISTER ↦□ globalKind : IProp GF) }}
      (App (Val (p @!! go.PointerType Register.ty @!! go!"IsInput")) (Val #()))
    {{ RET #(decide (kind.kind' = globalKind.kind'));
      p.[Register,go!"kind"] ↦{dq} kind ∗ globalAddr INPUT_REGISTER ↦□ globalKind }} := by
  wp_start as ⟨Hkind,#Hglobal⟩
  wp_auto
  iapply HΦ
  iframe Hkind Hglobal

theorem Register.isOutput_correct (p : Loc) (kind globalKind : Type') (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p.[Register,go!"kind"] ↦{dq} kind ∗ globalAddr OUTPUT_REGISTER ↦□ globalKind : IProp GF) }}
      (App (Val (p @!! go.PointerType Register.ty @!! go!"IsOutput")) (Val #()))
    {{ RET #(decide (kind.kind' = globalKind.kind'));
      p.[Register,go!"kind"] ↦{dq} kind ∗ globalAddr OUTPUT_REGISTER ↦□ globalKind }} := by
  wp_start as ⟨Hkind,#Hglobal⟩
  wp_auto
  iapply HΦ
  iframe Hkind Hglobal

#print axioms Register.name_correct
#print axioms Register.isNative_correct
#print axioms Register.width_correct
#print axioms Register.isInput_correct
#print axioms Register.isOutput_correct

theorem Register.native_record (p : Loc) (value : Register) (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p ↦{dq} value : IProp GF) }}
      (App (Val (p @!! go.PointerType Register.ty @!! go!"IsNative")) (Val #()))
    {{ RET #(decide (value.width' = W64 (2^64-1))); p ↦{dq} value }} := by
  wp_start as Hreg
  wp_auto
  rw [show W64 (2^64-1) = W64 18446744073709551615 from rfl]
  iapply HΦ $$ Hreg

theorem Register.input_record (p : Loc) (value : Register) (globalKind : Type')
    (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p ↦{dq} value ∗ globalAddr INPUT_REGISTER ↦□ globalKind : IProp GF) }}
      (App (Val (p @!! go.PointerType Register.ty @!! go!"IsInput")) (Val #()))
    {{ RET #(decide (value.kind'.kind' = globalKind.kind'));
      p ↦{dq} value ∗ globalAddr INPUT_REGISTER ↦□ globalKind }} := by
  wp_start as ⟨Hreg,#Hglobal⟩
  wp_auto
  iapply HΦ
  iframe Hreg Hglobal

theorem Register.output_record (p : Loc) (value : Register) (globalKind : Type')
    (dq : DFrac) (nonnull : p ≠ null) :
    {{ (p ↦{dq} value ∗ globalAddr OUTPUT_REGISTER ↦□ globalKind : IProp GF) }}
      (App (Val (p @!! go.PointerType Register.ty @!! go!"IsOutput")) (Val #()))
    {{ RET #(decide (value.kind'.kind' = globalKind.kind'));
      p ↦{dq} value ∗ globalAddr OUTPUT_REGISTER ↦□ globalKind }} := by
  wp_start as ⟨Hreg,#Hglobal⟩
  wp_auto
  iapply HΦ
  iframe Hreg Hglobal

#print axioms Register.native_record
#print axioms Register.input_record
#print axioms Register.output_record
end
end github_com.LFDT_Lineth.zkc.pkg.schema.register
end Perennial
