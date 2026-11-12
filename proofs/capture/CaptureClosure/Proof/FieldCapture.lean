module
public import CaptureClosure.Proof.Sub32
public import CaptureClosure.Code.github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear

@[expose] public section
noncomputable section
namespace Perennial
open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
namespace github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear

/-- Numerical value of a stored Montgomery limb; 1057030144 is R⁻¹ modulo p. -/
def decodedValue (raw : Nat) : Nat := raw * 1057030144 % 2130706433

theorem decoded_of_encoded (value : Nat) (bound : value < 2130706433) :
    decodedValue (value * 4294967296 % 2130706433) = value := by
  unfold decodedValue
  omega

private def reduction (raw : Nat) : Nat :=
  (raw + (raw * 2130706431 % 4294967296) * 2130706433) / 4294967296

private theorem reduction_bound (raw : Nat) (bound : raw < 4294967296) :
    reduction raw ≤ 2130706433 := by
  have ht := Nat.mod_lt (raw * 2130706431) (by decide : 0 < 4294967296)
  unfold reduction
  omega

private theorem reduction_value (raw : Nat) (bound : raw < 4294967296) :
    reduction raw % 2130706433 = decodedValue raw := by
  have ht := Nat.mod_lt (raw * 2130706431) (by decide : 0 < 4294967296)
  have he := Nat.mod_add_div (raw * 2130706431) 4294967296
  have hb := reduction_bound raw bound
  unfold reduction at hb ⊢
  unfold decodedValue
  omega

private def reductionWord (x : w64) : w32 :=
  W32 (uint.Z ((x + x * W64 2130706431 % W64 4294967296 * W64 2130706433) /
    W64 4294967296))

private theorem reductionWord_value (x : w64) (bound : x.toNat < 4294967296) :
    (reductionWord x).toNat = reduction x.toNat := by
  have hm := Nat.mod_lt (x.toNat * 2130706431) (by decide : 0 < 4294967296)
  have hp : (x * W64 2130706431).toNat = x.toNat * 2130706431 := by word
  have ht : (x * W64 2130706431 % W64 4294967296).toNat =
      x.toNat * 2130706431 % 4294967296 := by rw [BitVec.toNat_umod, hp]; rfl
  have htm : ((x * W64 2130706431 % W64 4294967296) * W64 2130706433).toNat =
      (x.toNat * 2130706431 % 4294967296) * 2130706433 := by
    rw [BitVec.toNat_mul, ht]
    change (_ * 2130706433) % 18446744073709551616 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hs : (x + x * W64 2130706431 % W64 4294967296 * W64 2130706433).toNat =
      x.toNat + (x.toNat * 2130706431 % 4294967296) * 2130706433 := by
    rw [BitVec.toNat_add, htm]
    exact Nat.mod_eq_of_lt (by omega)
  have hd : ((x + x * W64 2130706431 % W64 4294967296 * W64 2130706433) /
      W64 4294967296).toNat = reduction x.toNat := by
    rw [BitVec.toNat_udiv, hs]; rfl
  have hb := reduction_bound x.toNat bound
  unfold reductionWord
  rw [show uint.Z ((x + x * W64 2130706431 % W64 4294967296 * W64 2130706433) /
    W64 4294967296) = (reduction x.toNat : Int) from congrArg Int.ofNat hd]
  word

section
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [Element.TypeAssumptions]
variable [FuncUnfold montgomeryReduce [] montgomeryReduce.impl]
variable [FuncUnfold math.bits.Sub32 [] math.bits.Sub32.impl]

/-- Source-linked conversion used for constants and fixed tables in AIR capture. -/
theorem montgomery_capture (x : w64) (bound : x.toNat < 4294967296) :
    {{ (True : IProp GF) }}
      (App (Val (@! montgomeryReduce)) (Val #x))
    {{ RET #(array.mk 1 [W32 (decodedValue x.toNat)]); True }} := by
  have hw : (reductionWord x).toNat ≤ 2130706433 := by
    rw [reductionWord_value x bound]
    exact reduction_bound x.toNat bound
  wp_start
  wp_auto
  by_cases equal : (reductionWord x).toNat = 2130706433
  · have hexplicit : W32 (uint.Z ((x + x * W64 2130706431 % W64 4294967296 * W64 2130706433) /
        W64 4294967296)) = W32 2130706433 := BitVec.eq_of_toNat_eq equal
    rw [hexplicit]
    wp_apply sub32_at_modulus
    have hz : decodedValue x.toNat = 0 := by
      rw [← reduction_value x.toNat bound, ← reductionWord_value x bound, equal]
    rw [hz]
    rw [show array.mk 1 ((List.replicate 1 (zero_val w32)).set 0 (W32 0)) =
      array.mk 1 [W32 0] from rfl]
    wp_end
  · wp_apply sub32_below_modulus
    · change (reductionWord x).toNat < 2130706433
      omega
    have hr : reductionWord x = W32 (decodedValue x.toNat) := by
      apply BitVec.eq_of_toNat_eq
      have hsmall : reduction x.toNat < 2130706433 := by
        rw [← reductionWord_value x bound]
        omega
      have decoded := reduction_value x.toNat bound
      rw [Nat.mod_eq_of_lt hsmall] at decoded
      rw [reductionWord_value x bound, decoded]
      have hb : decodedValue x.toNat < 2130706433 := Nat.mod_lt _ (by decide)
      word
    have harray : array.mk 1 ((List.replicate 1 (zero_val w32)).set 0
        (W32 (uint.Z ((x + x * W64 2130706431 % W64 4294967296 * W64 2130706433) /
          W64 4294967296)))) = array.mk 1 [W32 (decodedValue x.toNat)] := by
      change array.mk 1 [reductionWord x] = _
      rw [hr]
    rw [harray]
    wp_end

/-- The actual `ToUint32` method removes the Montgomery representation. -/
theorem Element.toUint32_capture (raw : w32) :
    {{ (True : IProp GF) }}
      (App (Val ((array.mk 1 [raw]) @!! Element.ty @!! go!"ToUint32")) (Val #()))
    {{ RET #(W32 (decodedValue raw.toNat)); True }} := by
  wp_start
  wp_auto
  icases array_acc x_ptr 0 (DFrac.own 1) 1 (array.mk 1 [raw]) raw (by decide) rfl $$ x
    with ⟨Hx, _⟩
  rw [show sint.Z (W64 0) = 0 from rfl]
  wp_auto
  wp_apply (montgomery_capture (W64 (uint.Z raw)) (by word))
  rw [show (W64 (uint.Z raw)).toNat = raw.toNat by word]
  wp_end

/-- This is the conversion that the AIR exporter uses for constants and static tables. -/
theorem Element.uint64_capture (raw : w32) :
    {{ (True : IProp GF) }}
      (App (Val ((array.mk 1 [raw]) @!! Element.ty @!! go!"Uint64")) (Val #()))
    {{ RET #(W64 (decodedValue raw.toNat)); True }} := by
  wp_start
  wp_auto
  wp_apply Element.toUint32_capture raw
  have hb : decodedValue raw.toNat < 2130706433 := Nat.mod_lt _ (by decide)
  have heq : W64 (uint.Z (W32 (decodedValue raw.toNat))) = W64 (decodedValue raw.toNat) := by word
  rw [heq]
  wp_end

#print axioms montgomery_capture
#print axioms Element.toUint32_capture
#print axioms Element.uint64_capture
#print axioms decoded_of_encoded
end
end github_com.LFDT_Lineth.zkc.pkg.util.field.koalabear
end Perennial

