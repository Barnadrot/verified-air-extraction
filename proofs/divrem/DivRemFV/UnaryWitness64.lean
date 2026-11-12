import DivRemFV.UnsignedContract64
import DivRemFV.Generated.ReverseRows

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DivRemFV
open Generated

def absolute64Witness (h j k l col : Nat) : Nat :=
  match col with
  | 0 => h
  | 1 => j
  | 2 => k
  | 3 => l
  | 4 => if h < 32768 then h else 65535-h + (if j=0 ∧ k=0 ∧ l=0 then 1 else 0)
  | 5 => if h < 32768 then j else if k=0 ∧ l=0 then if j=0 then 0 else 65536-j else 65535-j
  | 6 => if h < 32768 then k else if l=0 then if k=0 then 0 else 65536-k else 65535-k
  | 7 => if h < 32768 then l else if l=0 then 0 else 65536-l
  | 8 => if h < 32768 then 0 else 1
  | 9 => 65535-h
  | 10 => 65535-j
  | 11 => 65535-k
  | 12 => 65535-l
  | 13 | 14 | 15 | 16 => 65535
  | 17 => h % 32768
  | 18 => j
  | 19 => k
  | 20 => l
  | 21 | 22 | 23 => 0
  | 24 => if l=0 then 1 else 0
  | 25 => if k=0 ∧ l=0 then 1 else 0
  | 26 => if j=0 ∧ k=0 ∧ l=0 then 1 else 0
  | 27 => 1
  | _ => 0

theorem absolute64_witness_bounds (h j k l : Nat)
    (hb : h < 65536) (jb : j < 65536) (kb : k < 65536) (lb : l < 65536) :
    Bounds55 (absolute64Witness h j k l) := by
  constructor <;> simp only [absolute64Witness] <;> (try split_ifs) <;> omega

theorem absolute64_witness_integer (h j k l : Nat)
    (hb : h < 65536) (jb : j < 65536) (kb : k < 65536) (lb : l < 65536) :
    IntegerEquations55 (fun col => (absolute64Witness h j k l col : Int)) := by
  by_cases sign : h < 32768 <;> by_cases jz : j=0 <;> by_cases kz : k=0 <;> by_cases lz : l=0 <;>
    constructor <;> norm_num [absolute64Witness,sign,jz,kz,lz] <;> omega

theorem absolute64_witness_field (h j k l : Nat)
    (hb : h < 65536) (jb : j < 65536) (kb : k < 65536) (lb : l < 65536) :
    Equations55 (fun col => (absolute64Witness h j k l col : K)) :=
  integer_to_field55 _ (absolute64_witness_integer h j k l hb jb kb lb)

theorem absolute64_witness_outside (h j k l col : Nat) (outside : 28 ≤ col) :
    absolute64Witness h j k l col = 0 := by
  unfold absolute64Witness
  split <;> omega

end DivRemFV
