import DivRemFV.Extension.ReverseRows
import DivRemFV.Extension.Construction
import DivRemFV.Extension.BoundsMap
import DivRemFV.SignedContract64

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV

def extend32Nat (a : Nat) : Nat := if a < 2147483648 then a else a+18446744069414584320

theorem extend32_toNat (a : BitVec 32) : extend32Nat a.toNat = (a.signExtend 64).toNat := by
  rw [BitVec.toNat_signExtend,BitVec.toNat_setWidth,BitVec.msb_eq_decide]
  simp only [decide_eq_true_eq]
  have cap := a.isLt
  change extend32Nat a.toNat = a.toNat % 18446744073709551616 +
    if 2147483648 ≤ a.toNat then 18446744069414584320 else 0
  rw [Nat.mod_eq_of_lt (by omega)]
  by_cases small : a.toNat < 2147483648
  · simp [extend32Nat,small,show ¬2147483648 ≤ a.toNat by omega]
  · simp [extend32Nat,small,show 2147483648 ≤ a.toNat by omega]

theorem signExtension_result (v : Nat → Nat) (bounds : Extension.Bounds67 v)
    (h : Extension.IntegerEquations67 (fun col => (v col : Int))) (active : v 9 ≠ 0) :
    wordValue v 2 = extend32Nat (pairValue v 0 1) := by
  have b0 := bounds.b0; have b1 := bounds.b1; have b2 := bounds.b2; have b3 := bounds.b3
  have b6 := bounds.b6; have b7 := bounds.b7; have b9 := bounds.b9
  have retOne : v 9=1 := by omega
  have ret : (v 9 : Int)=1 := by simp [retOne]
  have splitHigh := h.h12205
  have cases : v 6=0 ∨ v 6=1 := by omega
  rcases cases with zero | one
  · have sign : (v 6 : Int)=0 := by simp [zero]
    have lo := h.h12209; have hi := h.h12210; have upper := h.h12211
    simp only [ret,sign,one_mul,mul_one,sub_zero,zero_add] at lo hi upper splitHigh
    have threshold : pairValue v 0 1 < 2147483648 := by dsimp [pairValue]; omega
    dsimp [extend32Nat]
    rw [if_pos threshold]
    dsimp [pairValue,wordValue]
    omega
  · have sign : (v 6 : Int)=1 := by simp [one]
    have lo := h.h12206; have hi := h.h12207; have upper := h.h12208
    simp only [ret,sign,one_mul,mul_one,zero_add] at lo hi upper splitHigh
    have threshold : ¬pairValue v 0 1 < 2147483648 := by dsimp [pairValue]; omega
    dsimp [extend32Nat]
    rw [if_neg threshold]
    dsimp [pairValue,wordValue]
    omega

theorem signExtension_air_columns (tables : Tables) (row : Nat) (inside : row < (tables 67).size)
    (accepted : ConstraintsHold tables Extension.constraints) (fixed : StaticTablesFixed tables)
    (active : readCell tables 67 9 row ≠ 0) (a : BitVec 32)
    (input : (readCell tables 67 0 row,readCell tables 67 1 row) = encodePair a.toNat) :
    readFour tables 67 2 row = encodeFour (a.signExtend 64).toNat := by
  have ranges := fixed_tables_have_ranges tables fixed
  have bounds := Extension.bounds67 tables row inside accepted ranges
  have result := signExtension_result _ bounds (Extension.integer_equations67 tables row inside accepted ranges)
    (by intro zero; exact active (Fin.ext zero))
  have inputValue : pairValue (fun col => (readCell tables 67 col row).val) 0 1 = a.toNat := by
    have high := congrArg (fun d : Scalar × Scalar => d.1.val) input
    have low := congrArg (fun d : Scalar × Scalar => d.2.val) input
    dsimp only at high low
    dsimp [pairValue]
    rw [high,low]
    exact pair_encode_value a.toNat a.isLt
  rw [inputValue,extend32_toNat] at result
  have limbs := four_limbs (readCell tables 67 2 row) (readCell tables 67 3 row)
    (readCell tables 67 4 row) (readCell tables 67 5 row) bounds.b2 bounds.b3 bounds.b4 bounds.b5
  change _ = encodeFour (wordValue (fun col => (readCell tables 67 col row).val) 2) at limbs
  rw [result] at limbs
  exact limbs

def signExtensionWitness (h l col : Nat) : Nat :=
  match col with
  | 0 => h
  | 1 => l
  | 2 | 3 => if h < 32768 then 0 else 65535
  | 4 => h
  | 5 => l
  | 6 => if h < 32768 then 0 else 1
  | 7 => h%32768
  | 8 => l
  | 9 => 1
  | _ => 0

theorem signExtension_witness_bounds (h l : Nat) (hb : h < 65536) (lb : l < 65536) :
    Extension.Bounds67 (signExtensionWitness h l) := by
  constructor <;> simp only [signExtensionWitness] <;> (try split_ifs) <;> omega

theorem signExtension_witness_integer (h l : Nat) (hb : h < 65536) (lb : l < 65536) :
    Extension.IntegerEquations67 (fun col => (signExtensionWitness h l col : Int)) := by
  by_cases sign : h < 32768 <;>
    constructor <;> norm_num [signExtensionWitness,sign] <;> omega

theorem signExtension_witness_field (h l : Nat) (hb : h < 65536) (lb : l < 65536) :
    Extension.Equations67 (fun col => (signExtensionWitness h l col : K)) :=
  Extension.integer_to_field67 _ (signExtension_witness_integer h l hb lb)

theorem signExtension_witness_outside (h l col : Nat) (outside : 10 ≤ col) :
    signExtensionWitness h l col=0 := by
  unfold signExtensionWitness
  split <;> omega

end DivRemFV
