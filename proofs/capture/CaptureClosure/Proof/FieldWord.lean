module
public import CaptureClosure.Proof.FieldCapture

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear

opaque fieldWordSpec :
    { f : w32 → w64 // ∀ raw, f raw = W64 (decodedValue raw.toNat) } :=
  ⟨fun raw => W64 (decodedValue raw.toNat),fun _ => rfl⟩

def fieldWord (raw : w32) : w64 := fieldWordSpec.val raw

theorem fieldWord_value (raw : w32) : fieldWord raw = W64 (decodedValue raw.toNat) :=
  fieldWordSpec.property raw

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Element.TypeAssumptions]
variable [FuncUnfold montgomeryReduce [] montgomeryReduce.impl]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]

theorem Element.word_capture (raw : w32) :
    {{ (True : IProp GF) }}
      (App (Val ((array.mk 1 [raw]) @!! Element.ty @!! go!"Uint64")) (Val #()))
    {{ RET #(fieldWord raw); True }} := by
  simpa only [fieldWord_value] using Element.uint64_capture (GF := GF) raw

#print axioms fieldWord_value
#print axioms Element.word_capture
end
end github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear
end Perennial
