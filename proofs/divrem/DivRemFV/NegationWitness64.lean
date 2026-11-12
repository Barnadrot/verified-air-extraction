import DivRemFV.NegationWitness32

set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

namespace DivRemFV
open Generated

def negation64Witness (h j k l col : Nat) : Nat :=
  match col with
  | 0 => h
  | 1 => j
  | 2 => k
  | 3 => l
  | 4 => if h=0 ∧ j=0 ∧ k=0 ∧ l=0 then 0 else 65535-h + (if j=0 ∧ k=0 ∧ l=0 then 1 else 0)
  | 5 => if k=0 ∧ l=0 then if j=0 then 0 else 65536-j else 65535-j
  | 6 => if l=0 then if k=0 then 0 else 65536-k else 65535-k
  | 7 => if l=0 then 0 else 65536-l
  | 8 => if h < 32768 then 0 else 1
  | 9 => if h < 32768 then 65535 else 65535-h
  | 10 => if h < 32768 then 65535 else 65535-j
  | 11 => if h < 32768 then 65535 else 65535-k
  | 12 => if h < 32768 then 65535 else 65535-l
  | 13 => if h < 32768 then h - (if j=0 ∧ k=0 ∧ l=0 then 1 else 0) else 65535
  | 14 => if h < 32768 then if k=0 ∧ l=0 then if j=0 then 65535 else j-1 else j else 65535
  | 15 => if h < 32768 then if l=0 then if k=0 then 65535 else k-1 else k else 65535
  | 16 => if h < 32768 then if l=0 then 65535 else l-1 else 65535
  | 17 => h % 32768
  | 18 => j
  | 19 => k
  | 20 => l
  | 21 => if h=0 ∧ j=0 ∧ k=0 ∧ l=0 then 0 else 1
  | 22 => if h < 32768 ∧ l=0 then 1 else 0
  | 23 => if h < 32768 ∧ k=0 ∧ l=0 then 1 else 0
  | 24 => if h < 32768 ∧ j=0 ∧ k=0 ∧ l=0 then 1 else 0
  | 25 => if 32768 ≤ h ∧ l=0 then 1 else 0
  | 26 => if 32768 ≤ h ∧ k=0 ∧ l=0 then 1 else 0
  | 27 => if 32768 ≤ h ∧ j=0 ∧ k=0 ∧ l=0 then 1 else 0
  | 28 => 1
  | 29 => ((h+j+k+l : K)⁻¹).val
  | _ => 0

theorem negation64_witness_bounds (h j k l : Nat)
    (hb : h < 65536) (jb : j < 65536) (kb : k < 65536) (lb : l < 65536) :
    Bounds65 (negation64Witness h j k l) := by
  constructor <;> simp only [negation64Witness] <;> (try split_ifs) <;> omega

theorem negation64_witness_integer (h j k l : Nat)
    (hb : h < 65536) (jb : j < 65536) (kb : k < 65536) (lb : l < 65536) :
    IntegerEquations65 (fun col => (negation64Witness h j k l col : Int)) := by
  by_cases sign : h < 32768 <;> by_cases hz : h=0 <;> by_cases jz : j=0 <;>
    by_cases kz : k=0 <;> by_cases lz : l=0 <;>
    constructor <;> norm_num [negation64Witness,sign,hz,jz,kz,lz] <;> omega

theorem negation64_witness_field (h j k l : Nat)
    (hb : h < 65536) (jb : j < 65536) (kb : k < 65536) (lb : l < 65536) :
    Equations65 (fun col => (negation64Witness h j k l col : K)) := by
  apply integer_to_field65 _ (negation64_witness_integer h j k l hb jb kb lb)
  all_goals
    by_cases zero : h=0 ∧ j=0 ∧ k=0 ∧ l=0
    · obtain ⟨rfl,rfl,rfl,rfl⟩ := zero
      norm_num [negation64Witness]
    · have nonzero : (h : K) + (j : K) + (k : K) + (l : K) ≠ 0 := by
        intro eq
        have cast : ((h+j+k+l : Nat) : K) = 0 := by simpa only [Nat.cast_add] using eq
        have value := lift_field_equality _ 0 (by dsimp [fieldModulus]; omega) (by decide) cast
        omega
      have inverse := mul_inv_cancel₀ nonzero
      simpa only [negation64Witness,zero,↓reduceIte,zero_add,one_mul,mul_one,
        ZMod.natCast_zmod_val,inverse,sub_self,mul_zero]

theorem negation64_witness_outside (h j k l col : Nat) (outside : 30 ≤ col) :
    negation64Witness h j k l col = 0 := by
  unfold negation64Witness
  split <;> omega

end DivRemFV
