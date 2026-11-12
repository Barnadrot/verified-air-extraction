import DivRemFV.Spec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.ClearExcept

namespace DivRemFV

def magnitudeNat (width value : Nat) : Nat :=
  if value < 2 ^ (width - 1) then value else 2 ^ width - value

def negateNat (width value : Nat) : Nat :=
  if value = 0 then 0 else 2 ^ width - value

def signValue (width value : Nat) : Nat :=
  if value < 2 ^ (width - 1) then 0 else 1

def signedNatResult (width a b : Nat) : Nat × Nat :=
  if b = 0 then (2 ^ width - 1, a) else
  let q := magnitudeNat width a / magnitudeNat width b
  let r := magnitudeNat width a % magnitudeNat width b
  (if signValue width a = signValue width b then q else negateNat width q,
   if signValue width a = 0 then r else negateNat width r)

theorem magnitude_positive (width value : Nat) (positive : 0 < value) (bounded : value < 2 ^ width) :
    0 < magnitudeNat width value := by
  unfold magnitudeNat
  split <;> omega

theorem sign_from_digits (high rest base suffix sign : Nat)
    (restBound : rest < base) (suffixBound : suffix < 32768) (signBound : sign < 2)
    (splitHigh : (suffix : Int) + 32768 * (sign : Int) - (high : Int) = 0) :
    sign = (if base * high + rest < 32768 * base then 0 else 1) := by
  have cases : sign = 0 ∨ sign = 1 := by omega
  rcases cases with zero | one
  · have highBound : high ≤ 32767 := by omega
    have scaled := Nat.mul_le_mul_left base highBound
    have threshold : base * high + rest < 32768 * base := by nlinarith only [scaled, restBound]
    simp [threshold, zero]
  · have highBound : 32768 ≤ high := by omega
    have scaled := Nat.mul_le_mul_left base highBound
    have threshold : ¬base * high + rest < 32768 * base := by nlinarith only [scaled]
    simp [threshold, one]

def magnitudeAlgorithm {width : Nat} (a b : BitVec width) : BitVec width × BitVec width :=
  if b = 0 then (BitVec.allOnes width, a) else
    (if a.msb = b.msb then a.abs.udiv b.abs else -(a.abs.udiv b.abs),
     if a.msb = false then a.abs.umod b.abs else -(a.abs.umod b.abs))

theorem magnitudeNat_toNat {width : Nat} (a : BitVec width) :
    magnitudeNat width a.toNat = a.abs.toNat := by
  rw [BitVec.toNat_abs, BitVec.msb_eq_decide]
  by_cases low : a.toNat < 2 ^ (width - 1)
  · simp [magnitudeNat, low, Nat.not_le_of_lt low]
  · simp [magnitudeNat, low, Nat.le_of_not_gt low]

theorem signValue_toNat {width : Nat} (a : BitVec width) :
    signValue width a.toNat = (if a.msb then 1 else 0) := by
  rw [BitVec.msb_eq_decide]
  by_cases low : a.toNat < 2 ^ (width - 1)
  · simp [signValue, low, Nat.not_le_of_lt low]
  · simp [signValue, low, Nat.le_of_not_gt low]

theorem negateNat_toNat {width : Nat} (a : BitVec width) :
    negateNat width a.toNat = (-a).toNat := by
  rw [BitVec.toNat_neg]
  by_cases zero : a.toNat = 0
  · simp [negateNat, zero]
  · have positive : 0 < a.toNat := Nat.pos_of_ne_zero zero
    have bounded := a.isLt
    simp only [negateNat, zero, ↓reduceIte]
    rw [Nat.mod_eq_of_lt (by omega)]

theorem signedNat_toNat {width : Nat} (a b : BitVec width) :
    signedNatResult width a.toNat b.toNat =
      ((magnitudeAlgorithm a b).1.toNat, (magnitudeAlgorithm a b).2.toNat) := by
  by_cases zero : b = 0
  · subst b
    simp [signedNatResult, magnitudeAlgorithm, BitVec.toNat_allOnes]
  · have naturalNonzero : b.toNat ≠ 0 := by
      intro equal
      apply zero
      apply BitVec.toNat_inj.mp
      simpa using equal
    simp only [signedNatResult, magnitudeAlgorithm, zero, naturalNonzero, ↓reduceIte,
      magnitudeNat_toNat, signValue_toNat]
    rw [← BitVec.toNat_udiv, ← BitVec.toNat_umod]
    cases ha : a.msb <;> cases hb : b.msb <;>
      simp only [ha, hb, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte,
        Nat.zero_ne_one, Nat.one_ne_zero, Prod.fst, Prod.snd, negateNat_toNat] <;> rfl

theorem magnitudeAlgorithm_nonzero {width : Nat} (a b : BitVec width) (nonzero : b ≠ 0) :
    magnitudeAlgorithm a b = (a.sdiv b, a.srem b) := by
  unfold magnitudeAlgorithm BitVec.sdiv BitVec.srem BitVec.abs
  simp only [nonzero, ↓reduceIte]
  cases a.msb <;> cases b.msb <;> simp

theorem sdiv_integer {width : Nat} (a b : BitVec width) :
    a.sdiv b = BitVec.ofInt width (a.toInt.tdiv b.toInt) := by
  apply BitVec.toInt_inj.mp
  rw [BitVec.toInt_sdiv, BitVec.toInt_ofInt]

theorem srem_integer {width : Nat} (a b : BitVec width) :
    a.srem b = BitVec.ofInt width (a.toInt.tmod b.toInt) := by
  rw [← BitVec.toInt_srem]
  exact BitVec.ofInt_toInt.symm

theorem magnitudeAlgorithm_arch64 (a b : BitVec 64) :
    magnitudeAlgorithm a b = (signedQuotient a b, signedRemainder a b) := by
  by_cases zero : b = 0
  · subst b
    simp [magnitudeAlgorithm, signedQuotient, signedRemainder]
  · rw [magnitudeAlgorithm_nonzero a b zero]
    unfold signedQuotient signedRemainder
    simp only [zero, ↓reduceIte]
    by_cases overflow : a = BitVec.intMin 64 ∧ b = BitVec.allOnes 64
    · rcases overflow with ⟨rfl,rfl⟩
      decide
    · simp only [overflow, ↓reduceIte]
      exact Prod.ext (sdiv_integer a b) (srem_integer a b)

theorem magnitudeAlgorithm_arch32 (a b : BitVec 32) :
    magnitudeAlgorithm a b = (signedQuotient a b, signedRemainder a b) := by
  by_cases zero : b = 0
  · subst b
    simp [magnitudeAlgorithm, signedQuotient, signedRemainder]
  · rw [magnitudeAlgorithm_nonzero a b zero]
    unfold signedQuotient signedRemainder
    simp only [zero, ↓reduceIte]
    by_cases overflow : a = BitVec.intMin 32 ∧ b = BitVec.allOnes 32
    · rcases overflow with ⟨rfl,rfl⟩
      decide
    · simp only [overflow, ↓reduceIte]
      exact Prod.ext (sdiv_integer a b) (srem_integer a b)

end DivRemFV
