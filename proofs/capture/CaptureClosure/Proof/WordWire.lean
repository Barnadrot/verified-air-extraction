module
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory
public import Perennial.Std.Word.LittleEndian
public import CaptureClosure.Code.divremfv.internal.airdata

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace divremfv.internal.airdata.SourceCapture

theorem little_endian_bytes (v : w64) :
    u64Le v = [W8 (uint.Z v), W8 (uint.Z (v >>> W64 8)), W8 (uint.Z (v >>> W64 16)),
      W8 (uint.Z (v >>> W64 24)), W8 (uint.Z (v >>> W64 32)), W8 (uint.Z (v >>> W64 40)),
      W8 (uint.Z (v >>> W64 48)), W8 (uint.Z (v >>> W64 56))] := by
  simp only [u64Le, u64LeDef, LittleEndian.split, W8, uint.Z, BitVec.ofInt_natCast, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | trivial | (apply BitVec.eq_of_toNat_eq; simp; omega)

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [FuncUnfold appendWireWord [] appendWireWord.impl]

theorem append_word (out : GoSlice) (prior : List w8) (value : w64) :
    {{ (out ↦* prior ∗ ownSliceCap w8 out (DFrac.own 1) : IProp GF) }}
      (App (App (Val (@! appendWireWord)) (Val #out)) (Val #value))
    {{ (result : GoSlice), RET #result;
      result ↦* (prior ++ u64Le value) ∗ ownSliceCap w8 result (DFrac.own 1) }} := by
  wp_start as ⟨Hout, Hcap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) (u64Le value)
  wp_auto
  isplitl []
  · ipureintro
    rw [little_endian_bytes]
    rfl
  iintro %bytes ⟨Hbytes, HbytesCap⟩
  wp_auto
  wp_apply wp_slice_append (V := w8) (st := go.SliceType go.byte) (t := go.byte) out prior
    _ (u64Le value) (DFrac.own 1)
    $$ [Hout Hcap Hbytes] with %result ⟨Hresult,HresultCap,Hbytes⟩
  · iframe Hout Hcap Hbytes
  iapply HΦ
  iframe Hresult HresultCap

#print axioms append_word
end
end divremfv.internal.airdata.SourceCapture
end Perennial
