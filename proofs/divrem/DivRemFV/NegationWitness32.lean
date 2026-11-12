import DivRemFV.UnaryWitness64

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DivRemFV
open Generated

def negation32Witness (h l col : Nat) : Nat :=
  match col with
  | 0 => h
  | 1 => l
  | 2 => if h=0 ∧ l=0 then 0 else 65535-h + (if l=0 then 1 else 0)
  | 3 => if l=0 then 0 else 65536-l
  | 4 => if h < 32768 then 0 else 1
  | 5 => if h < 32768 then 65535 else 65535-h
  | 6 => if h < 32768 then 65535 else 65535-l
  | 7 => if h < 32768 then h - (if l=0 then 1 else 0) else 65535
  | 8 => if h < 32768 then if l=0 then 65535 else l-1 else 65535
  | 9 => h % 32768
  | 10 => l
  | 11 => if h=0 ∧ l=0 then 0 else 1
  | 12 => if h < 32768 ∧ l=0 then 1 else 0
  | 13 => if 32768 ≤ h ∧ l=0 then 1 else 0
  | 14 => 1
  | 15 => ((h+l : K)⁻¹).val
  | _ => 0

theorem negation32_witness_bounds (h l : Nat) (hb : h < 65536) (lb : l < 65536) :
    Bounds66 (negation32Witness h l) := by
  constructor <;> simp only [negation32Witness] <;> (try split_ifs) <;> omega

theorem negation32_witness_integer (h l : Nat) (hb : h < 65536) (lb : l < 65536) :
    IntegerEquations66 (fun col => (negation32Witness h l col : Int)) := by
  by_cases sign : h < 32768 <;> by_cases hz : h=0 <;> by_cases lz : l=0 <;>
    constructor <;> norm_num [negation32Witness,sign,hz,lz] <;> omega

theorem negation32_witness_field (h l : Nat) (hb : h < 65536) (lb : l < 65536) :
    Equations66 (fun col => (negation32Witness h l col : K)) := by
  apply integer_to_field66 _ (negation32_witness_integer h l hb lb)
  all_goals
    by_cases zero : h=0 ∧ l=0
    · obtain ⟨rfl,rfl⟩ := zero
      norm_num [negation32Witness]
    · have nonzero : (h : K) + (l : K) ≠ 0 := by
        intro eq
        have cast : ((h+l : Nat) : K) = 0 := by simpa only [Nat.cast_add] using eq
        have value := lift_field_equality _ 0 (by dsimp [fieldModulus]; omega) (by decide) cast
        omega
      have inverse := mul_inv_cancel₀ nonzero
      simpa only [negation32Witness,zero,↓reduceIte,zero_add,one_mul,mul_one,
        ZMod.natCast_zmod_val,inverse,sub_self,mul_zero]

theorem negation32_witness_outside (h l col : Nat) (outside : 16 ≤ col) :
    negation32Witness h l col = 0 := by
  unfold negation32Witness
  split <;> omega

end DivRemFV
