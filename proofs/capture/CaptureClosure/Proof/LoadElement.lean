module
public import CaptureClosure.Proof.FieldCapture

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture
open github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Element.TypeAssumptions]

theorem load_element (sl : GoSlice) (index : Int) (values : List (GoArray w32 1))
    (raw : w32) (dq : DFrac) (nonnegative : 0 ≤ index) :
    {{ (sl ↦*{dq} values ∗ ⌜values[index.toNat]? = some (array.mk 1 [raw])⌝ : IProp GF) }}
      (App (Val (GoInstruction (GoLoad Element.ty)))
        (Val #(sliceIndexRef (GoArray w32 1) index sl)))
    {{ RET #(array.mk 1 [raw]); sl ↦*{dq} values }} :=
  wp_load_slice_index (V := GoArray w32 1) (t := Element.ty)
    sl index values dq (array.mk 1 [raw]) nonnegative

#print axioms load_element
end
end divremfv.internal.airdata.SourceCapture
end Perennial
