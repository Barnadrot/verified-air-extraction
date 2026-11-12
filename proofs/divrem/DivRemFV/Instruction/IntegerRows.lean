import DivRemFV.Instruction.Artifact
import DivRemFV.Intervals
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DivRemFV.Instruction

def intervals41 : Array Interval := #[
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 255⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 31⟩,
  ⟨0, 31⟩,
  ⟨0, 31⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1023⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 63⟩,
  ⟨0, 2047⟩,
  ⟨0, 31⟩,
  ⟨0, 1⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 32767⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 65535⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1023⟩,
  ⟨0, 1023⟩,
  ⟨0, 1023⟩,
  ⟨0, 1023⟩,
  ⟨0, 2047⟩,
  ⟨0, 2047⟩,
  ⟨0, 0⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 1⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩,
  ⟨0, 2130706432⟩
]
def columns41 (col : Nat) : Interval := intervals41[col]?.getD ⟨0, 2130706432⟩

theorem column_bounds41 (tables : Tables) (row : Nat)
    (inside : row < (tables 41).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    ∀ col, (columns41 col).Contains ((readCell tables 41 col row).val : Int) := by
  intro col
  have bound := (readCell tables 41 col row).isLt
  have nonnegative : (0 : Int) ≤ (readCell tables 41 col row).val := by omega
  by_cases small : col < 181
  · have bounds := bounds41 tables row inside accepted ranges
    interval_cases col
    · change (0 : Int) ≤ (readCell tables 41 0 row).val ∧
        ((readCell tables 41 0 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b0; omega
    · change (0 : Int) ≤ (readCell tables 41 1 row).val ∧
        ((readCell tables 41 1 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b1; omega
    · change (0 : Int) ≤ (readCell tables 41 2 row).val ∧
        ((readCell tables 41 2 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b2; omega
    · change (0 : Int) ≤ (readCell tables 41 3 row).val ∧
        ((readCell tables 41 3 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b3; omega
    · change (0 : Int) ≤ (readCell tables 41 4 row).val ∧
        ((readCell tables 41 4 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b4; omega
    · change (0 : Int) ≤ (readCell tables 41 5 row).val ∧
        ((readCell tables 41 5 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b5; omega
    · change (0 : Int) ≤ (readCell tables 41 6 row).val ∧
        ((readCell tables 41 6 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b6; omega
    · change (0 : Int) ≤ (readCell tables 41 7 row).val ∧
        ((readCell tables 41 7 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b7; omega
    · change (0 : Int) ≤ (readCell tables 41 8 row).val ∧
        ((readCell tables 41 8 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b8; omega
    · change (0 : Int) ≤ (readCell tables 41 9 row).val ∧
        ((readCell tables 41 9 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b9; omega
    · change (0 : Int) ≤ (readCell tables 41 10 row).val ∧
        ((readCell tables 41 10 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b10; omega
    · change (0 : Int) ≤ (readCell tables 41 11 row).val ∧
        ((readCell tables 41 11 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b11; omega
    · change (0 : Int) ≤ (readCell tables 41 12 row).val ∧
        ((readCell tables 41 12 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b12; omega
    · change (0 : Int) ≤ (readCell tables 41 13 row).val ∧
        ((readCell tables 41 13 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b13; omega
    · change (0 : Int) ≤ (readCell tables 41 14 row).val ∧
        ((readCell tables 41 14 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b14; omega
    · change (0 : Int) ≤ (readCell tables 41 15 row).val ∧
        ((readCell tables 41 15 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b15; omega
    · change (0 : Int) ≤ (readCell tables 41 16 row).val ∧
        ((readCell tables 41 16 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b16; omega
    · change (0 : Int) ≤ (readCell tables 41 17 row).val ∧
        ((readCell tables 41 17 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b17; omega
    · change (0 : Int) ≤ (readCell tables 41 18 row).val ∧
        ((readCell tables 41 18 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b18; omega
    · change (0 : Int) ≤ (readCell tables 41 19 row).val ∧
        ((readCell tables 41 19 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b19; omega
    · change (0 : Int) ≤ (readCell tables 41 20 row).val ∧
        ((readCell tables 41 20 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b20; omega
    · change (0 : Int) ≤ (readCell tables 41 21 row).val ∧
        ((readCell tables 41 21 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b21; omega
    · change (0 : Int) ≤ (readCell tables 41 22 row).val ∧
        ((readCell tables 41 22 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b22; omega
    · change (0 : Int) ≤ (readCell tables 41 23 row).val ∧
        ((readCell tables 41 23 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b23; omega
    · change (0 : Int) ≤ (readCell tables 41 24 row).val ∧
        ((readCell tables 41 24 row).val : Int) ≤ 255
      constructor
      · omega
      · have width := bounds.b24; omega
    · change (0 : Int) ≤ (readCell tables 41 25 row).val ∧
        ((readCell tables 41 25 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b25; omega
    · change (0 : Int) ≤ (readCell tables 41 26 row).val ∧
        ((readCell tables 41 26 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b26; omega
    · change (0 : Int) ≤ (readCell tables 41 27 row).val ∧
        ((readCell tables 41 27 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b27; omega
    · change (0 : Int) ≤ (readCell tables 41 28 row).val ∧
        ((readCell tables 41 28 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b28; omega
    · change (0 : Int) ≤ (readCell tables 41 29 row).val ∧
        ((readCell tables 41 29 row).val : Int) ≤ 31
      constructor
      · omega
      · have width := bounds.b29; omega
    · change (0 : Int) ≤ (readCell tables 41 30 row).val ∧
        ((readCell tables 41 30 row).val : Int) ≤ 31
      constructor
      · omega
      · have width := bounds.b30; omega
    · change (0 : Int) ≤ (readCell tables 41 31 row).val ∧
        ((readCell tables 41 31 row).val : Int) ≤ 31
      constructor
      · omega
      · have width := bounds.b31; omega
    · change (0 : Int) ≤ (readCell tables 41 32 row).val ∧
        ((readCell tables 41 32 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b32; omega
    · change (0 : Int) ≤ (readCell tables 41 33 row).val ∧
        ((readCell tables 41 33 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b33; omega
    · change (0 : Int) ≤ (readCell tables 41 34 row).val ∧
        ((readCell tables 41 34 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b34; omega
    · change (0 : Int) ≤ (readCell tables 41 35 row).val ∧
        ((readCell tables 41 35 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b35; omega
    · change (0 : Int) ≤ (readCell tables 41 36 row).val ∧
        ((readCell tables 41 36 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b36; omega
    · change (0 : Int) ≤ (readCell tables 41 37 row).val ∧
        ((readCell tables 41 37 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b37; omega
    · change (0 : Int) ≤ (readCell tables 41 38 row).val ∧
        ((readCell tables 41 38 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b38; omega
    · change (0 : Int) ≤ (readCell tables 41 39 row).val ∧
        ((readCell tables 41 39 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b39; omega
    · change (0 : Int) ≤ (readCell tables 41 40 row).val ∧
        ((readCell tables 41 40 row).val : Int) ≤ 1023
      constructor
      · omega
      · have width := bounds.b40; omega
    · change (0 : Int) ≤ (readCell tables 41 41 row).val ∧
        ((readCell tables 41 41 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b41; omega
    · change (0 : Int) ≤ (readCell tables 41 42 row).val ∧
        ((readCell tables 41 42 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b42; omega
    · change (0 : Int) ≤ (readCell tables 41 43 row).val ∧
        ((readCell tables 41 43 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b43; omega
    · change (0 : Int) ≤ (readCell tables 41 44 row).val ∧
        ((readCell tables 41 44 row).val : Int) ≤ 63
      constructor
      · omega
      · have width := bounds.b44; omega
    · change (0 : Int) ≤ (readCell tables 41 45 row).val ∧
        ((readCell tables 41 45 row).val : Int) ≤ 2047
      constructor
      · omega
      · have width := bounds.b45; omega
    · change (0 : Int) ≤ (readCell tables 41 46 row).val ∧
        ((readCell tables 41 46 row).val : Int) ≤ 31
      constructor
      · omega
      · have width := bounds.b46; omega
    · change (0 : Int) ≤ (readCell tables 41 47 row).val ∧
        ((readCell tables 41 47 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b47; omega
    · change (0 : Int) ≤ (readCell tables 41 48 row).val ∧
        ((readCell tables 41 48 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b48; omega
    · change (0 : Int) ≤ (readCell tables 41 49 row).val ∧
        ((readCell tables 41 49 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b49; omega
    · change (0 : Int) ≤ (readCell tables 41 50 row).val ∧
        ((readCell tables 41 50 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b50; omega
    · change (0 : Int) ≤ (readCell tables 41 51 row).val ∧
        ((readCell tables 41 51 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b51; omega
    · change (0 : Int) ≤ (readCell tables 41 52 row).val ∧
        ((readCell tables 41 52 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b52; omega
    · change (0 : Int) ≤ (readCell tables 41 53 row).val ∧
        ((readCell tables 41 53 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b53; omega
    · change (0 : Int) ≤ (readCell tables 41 54 row).val ∧
        ((readCell tables 41 54 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b54; omega
    · change (0 : Int) ≤ (readCell tables 41 55 row).val ∧
        ((readCell tables 41 55 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b55; omega
    · change (0 : Int) ≤ (readCell tables 41 56 row).val ∧
        ((readCell tables 41 56 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b56; omega
    · change (0 : Int) ≤ (readCell tables 41 57 row).val ∧
        ((readCell tables 41 57 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b57; omega
    · change (0 : Int) ≤ (readCell tables 41 58 row).val ∧
        ((readCell tables 41 58 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b58; omega
    · change (0 : Int) ≤ (readCell tables 41 59 row).val ∧
        ((readCell tables 41 59 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b59; omega
    · change (0 : Int) ≤ (readCell tables 41 60 row).val ∧
        ((readCell tables 41 60 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b60; omega
    · change (0 : Int) ≤ (readCell tables 41 61 row).val ∧
        ((readCell tables 41 61 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b61; omega
    · change (0 : Int) ≤ (readCell tables 41 62 row).val ∧
        ((readCell tables 41 62 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b62; omega
    · change (0 : Int) ≤ (readCell tables 41 63 row).val ∧
        ((readCell tables 41 63 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b63; omega
    · change (0 : Int) ≤ (readCell tables 41 64 row).val ∧
        ((readCell tables 41 64 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b64; omega
    · change (0 : Int) ≤ (readCell tables 41 65 row).val ∧
        ((readCell tables 41 65 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b65; omega
    · change (0 : Int) ≤ (readCell tables 41 66 row).val ∧
        ((readCell tables 41 66 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b66; omega
    · change (0 : Int) ≤ (readCell tables 41 67 row).val ∧
        ((readCell tables 41 67 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b67; omega
    · change (0 : Int) ≤ (readCell tables 41 68 row).val ∧
        ((readCell tables 41 68 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b68; omega
    · change (0 : Int) ≤ (readCell tables 41 69 row).val ∧
        ((readCell tables 41 69 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b69; omega
    · change (0 : Int) ≤ (readCell tables 41 70 row).val ∧
        ((readCell tables 41 70 row).val : Int) ≤ 32767
      constructor
      · omega
      · have width := bounds.b70; omega
    · change (0 : Int) ≤ (readCell tables 41 71 row).val ∧
        ((readCell tables 41 71 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b71; omega
    · change (0 : Int) ≤ (readCell tables 41 72 row).val ∧
        ((readCell tables 41 72 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b72; omega
    · change (0 : Int) ≤ (readCell tables 41 73 row).val ∧
        ((readCell tables 41 73 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b73; omega
    · change (0 : Int) ≤ (readCell tables 41 74 row).val ∧
        ((readCell tables 41 74 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b74; omega
    · change (0 : Int) ≤ (readCell tables 41 75 row).val ∧
        ((readCell tables 41 75 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b75; omega
    · change (0 : Int) ≤ (readCell tables 41 76 row).val ∧
        ((readCell tables 41 76 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b76; omega
    · change (0 : Int) ≤ (readCell tables 41 77 row).val ∧
        ((readCell tables 41 77 row).val : Int) ≤ 65535
      constructor
      · omega
      · have width := bounds.b77; omega
    · change (0 : Int) ≤ (readCell tables 41 78 row).val ∧
        ((readCell tables 41 78 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b78; omega
    · change (0 : Int) ≤ (readCell tables 41 79 row).val ∧
        ((readCell tables 41 79 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b79; omega
    · change (0 : Int) ≤ (readCell tables 41 80 row).val ∧
        ((readCell tables 41 80 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b80; omega
    · change (0 : Int) ≤ (readCell tables 41 81 row).val ∧
        ((readCell tables 41 81 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b81; omega
    · change (0 : Int) ≤ (readCell tables 41 82 row).val ∧
        ((readCell tables 41 82 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b82; omega
    · change (0 : Int) ≤ (readCell tables 41 83 row).val ∧
        ((readCell tables 41 83 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b83; omega
    · change (0 : Int) ≤ (readCell tables 41 84 row).val ∧
        ((readCell tables 41 84 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b84; omega
    · change (0 : Int) ≤ (readCell tables 41 85 row).val ∧
        ((readCell tables 41 85 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b85; omega
    · change (0 : Int) ≤ (readCell tables 41 86 row).val ∧
        ((readCell tables 41 86 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b86; omega
    · change (0 : Int) ≤ (readCell tables 41 87 row).val ∧
        ((readCell tables 41 87 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b87; omega
    · change (0 : Int) ≤ (readCell tables 41 88 row).val ∧
        ((readCell tables 41 88 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b88; omega
    · change (0 : Int) ≤ (readCell tables 41 89 row).val ∧
        ((readCell tables 41 89 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b89; omega
    · change (0 : Int) ≤ (readCell tables 41 90 row).val ∧
        ((readCell tables 41 90 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b90; omega
    · change (0 : Int) ≤ (readCell tables 41 91 row).val ∧
        ((readCell tables 41 91 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b91; omega
    · change (0 : Int) ≤ (readCell tables 41 92 row).val ∧
        ((readCell tables 41 92 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b92; omega
    · change (0 : Int) ≤ (readCell tables 41 93 row).val ∧
        ((readCell tables 41 93 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b93; omega
    · change (0 : Int) ≤ (readCell tables 41 94 row).val ∧
        ((readCell tables 41 94 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b94; omega
    · change (0 : Int) ≤ (readCell tables 41 95 row).val ∧
        ((readCell tables 41 95 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b95; omega
    · change (0 : Int) ≤ (readCell tables 41 96 row).val ∧
        ((readCell tables 41 96 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b96; omega
    · change (0 : Int) ≤ (readCell tables 41 97 row).val ∧
        ((readCell tables 41 97 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b97; omega
    · change (0 : Int) ≤ (readCell tables 41 98 row).val ∧
        ((readCell tables 41 98 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b98; omega
    · change (0 : Int) ≤ (readCell tables 41 99 row).val ∧
        ((readCell tables 41 99 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b99; omega
    · change (0 : Int) ≤ (readCell tables 41 100 row).val ∧
        ((readCell tables 41 100 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b100; omega
    · change (0 : Int) ≤ (readCell tables 41 101 row).val ∧
        ((readCell tables 41 101 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b101; omega
    · change (0 : Int) ≤ (readCell tables 41 102 row).val ∧
        ((readCell tables 41 102 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b102; omega
    · change (0 : Int) ≤ (readCell tables 41 103 row).val ∧
        ((readCell tables 41 103 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b103; omega
    · change (0 : Int) ≤ (readCell tables 41 104 row).val ∧
        ((readCell tables 41 104 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b104; omega
    · change (0 : Int) ≤ (readCell tables 41 105 row).val ∧
        ((readCell tables 41 105 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b105; omega
    · change (0 : Int) ≤ (readCell tables 41 106 row).val ∧
        ((readCell tables 41 106 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b106; omega
    · change (0 : Int) ≤ (readCell tables 41 107 row).val ∧
        ((readCell tables 41 107 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b107; omega
    · change (0 : Int) ≤ (readCell tables 41 108 row).val ∧
        ((readCell tables 41 108 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b108; omega
    · change (0 : Int) ≤ (readCell tables 41 109 row).val ∧
        ((readCell tables 41 109 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b109; omega
    · change (0 : Int) ≤ (readCell tables 41 110 row).val ∧
        ((readCell tables 41 110 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b110; omega
    · change (0 : Int) ≤ (readCell tables 41 111 row).val ∧
        ((readCell tables 41 111 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b111; omega
    · change (0 : Int) ≤ (readCell tables 41 112 row).val ∧
        ((readCell tables 41 112 row).val : Int) ≤ 1023
      constructor
      · omega
      · have width := bounds.b112; omega
    · change (0 : Int) ≤ (readCell tables 41 113 row).val ∧
        ((readCell tables 41 113 row).val : Int) ≤ 1023
      constructor
      · omega
      · have width := bounds.b113; omega
    · change (0 : Int) ≤ (readCell tables 41 114 row).val ∧
        ((readCell tables 41 114 row).val : Int) ≤ 1023
      constructor
      · omega
      · have width := bounds.b114; omega
    · change (0 : Int) ≤ (readCell tables 41 115 row).val ∧
        ((readCell tables 41 115 row).val : Int) ≤ 1023
      constructor
      · omega
      · have width := bounds.b115; omega
    · change (0 : Int) ≤ (readCell tables 41 116 row).val ∧
        ((readCell tables 41 116 row).val : Int) ≤ 2047
      constructor
      · omega
      · have width := bounds.b116; omega
    · change (0 : Int) ≤ (readCell tables 41 117 row).val ∧
        ((readCell tables 41 117 row).val : Int) ≤ 2047
      constructor
      · omega
      · have width := bounds.b117; omega
    · change (0 : Int) ≤ (readCell tables 41 118 row).val ∧
        ((readCell tables 41 118 row).val : Int) ≤ 0
      constructor
      · omega
      · have width := bounds.b118; omega
    · change (0 : Int) ≤ (readCell tables 41 119 row).val ∧
        ((readCell tables 41 119 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b119; omega
    · change (0 : Int) ≤ (readCell tables 41 120 row).val ∧
        ((readCell tables 41 120 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b120; omega
    · change (0 : Int) ≤ (readCell tables 41 121 row).val ∧
        ((readCell tables 41 121 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b121; omega
    · change (0 : Int) ≤ (readCell tables 41 122 row).val ∧
        ((readCell tables 41 122 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b122; omega
    · change (0 : Int) ≤ (readCell tables 41 123 row).val ∧
        ((readCell tables 41 123 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b123; omega
    · change (0 : Int) ≤ (readCell tables 41 124 row).val ∧
        ((readCell tables 41 124 row).val : Int) ≤ 1
      constructor
      · omega
      · have width := bounds.b124; omega
    · change (0 : Int) ≤ (readCell tables 41 125 row).val ∧
        ((readCell tables 41 125 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 126 row).val ∧
        ((readCell tables 41 126 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 127 row).val ∧
        ((readCell tables 41 127 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 128 row).val ∧
        ((readCell tables 41 128 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 129 row).val ∧
        ((readCell tables 41 129 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 130 row).val ∧
        ((readCell tables 41 130 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 131 row).val ∧
        ((readCell tables 41 131 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 132 row).val ∧
        ((readCell tables 41 132 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 133 row).val ∧
        ((readCell tables 41 133 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 134 row).val ∧
        ((readCell tables 41 134 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 135 row).val ∧
        ((readCell tables 41 135 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 136 row).val ∧
        ((readCell tables 41 136 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 137 row).val ∧
        ((readCell tables 41 137 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 138 row).val ∧
        ((readCell tables 41 138 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 139 row).val ∧
        ((readCell tables 41 139 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 140 row).val ∧
        ((readCell tables 41 140 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 141 row).val ∧
        ((readCell tables 41 141 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 142 row).val ∧
        ((readCell tables 41 142 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 143 row).val ∧
        ((readCell tables 41 143 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 144 row).val ∧
        ((readCell tables 41 144 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 145 row).val ∧
        ((readCell tables 41 145 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 146 row).val ∧
        ((readCell tables 41 146 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 147 row).val ∧
        ((readCell tables 41 147 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 148 row).val ∧
        ((readCell tables 41 148 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 149 row).val ∧
        ((readCell tables 41 149 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 150 row).val ∧
        ((readCell tables 41 150 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 151 row).val ∧
        ((readCell tables 41 151 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 152 row).val ∧
        ((readCell tables 41 152 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 153 row).val ∧
        ((readCell tables 41 153 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 154 row).val ∧
        ((readCell tables 41 154 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 155 row).val ∧
        ((readCell tables 41 155 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 156 row).val ∧
        ((readCell tables 41 156 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 157 row).val ∧
        ((readCell tables 41 157 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 158 row).val ∧
        ((readCell tables 41 158 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 159 row).val ∧
        ((readCell tables 41 159 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 160 row).val ∧
        ((readCell tables 41 160 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 161 row).val ∧
        ((readCell tables 41 161 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 162 row).val ∧
        ((readCell tables 41 162 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 163 row).val ∧
        ((readCell tables 41 163 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 164 row).val ∧
        ((readCell tables 41 164 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 165 row).val ∧
        ((readCell tables 41 165 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 166 row).val ∧
        ((readCell tables 41 166 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 167 row).val ∧
        ((readCell tables 41 167 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 168 row).val ∧
        ((readCell tables 41 168 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 169 row).val ∧
        ((readCell tables 41 169 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 170 row).val ∧
        ((readCell tables 41 170 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 171 row).val ∧
        ((readCell tables 41 171 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 172 row).val ∧
        ((readCell tables 41 172 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 173 row).val ∧
        ((readCell tables 41 173 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 174 row).val ∧
        ((readCell tables 41 174 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 175 row).val ∧
        ((readCell tables 41 175 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 176 row).val ∧
        ((readCell tables 41 176 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 177 row).val ∧
        ((readCell tables 41 177 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 178 row).val ∧
        ((readCell tables 41 178 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 179 row).val ∧
        ((readCell tables 41 179 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
    · change (0 : Int) ≤ (readCell tables 41 180 row).val ∧
        ((readCell tables 41 180 row).val : Int) ≤ 2130706432
      constructor
      · omega
      · dsimp [fieldModulus] at bound; omega
  · have missing : intervals41[col]? = none := by
      apply Array.getElem?_eq_none
      simpa [intervals41] using Nat.le_of_not_gt small
    simp only [columns41, missing, Option.getD_none, Interval.Contains]
    constructor
    · exact nonnegative
    · dsimp [fieldModulus] at bound; omega

structure IntegerEquations41 (v : Nat → Int) : Prop where
  h9224 : (((1 : Int) * (v 124)) * (((((0 : Int) + (v 74)) + (((1 : Int) * (65536 : Int)) * (v 106))) - (v 2)) - (1 : Int))) = 0
  h9225 : (((1 : Int) * (v 124)) * (((((0 : Int) + (v 73)) + (((1 : Int) * (65536 : Int)) * (v 107))) - (v 1)) - (v 106))) = 0
  h9226 : (((1 : Int) * (v 124)) * (((v 72) - (v 0)) - (v 107))) = 0
  h9227 : (((1 : Int) * (v 124)) * (((((0 : Int) + (v 77)) + (((1 : Int) * (65536 : Int)) * (v 108))) - (v 2)) - (2 : Int))) = 0
  h9228 : (((1 : Int) * (v 124)) * (((((0 : Int) + (v 76)) + (((1 : Int) * (65536 : Int)) * (v 109))) - (v 1)) - (v 108))) = 0
  h9229 : (((1 : Int) * (v 124)) * (((v 75) - (v 0)) - (v 109))) = 0
  h9230 : ((((1 : Int) * (v 124)) * ((v 24) - (28 : Int))) * (v 78)) = 0
  h9232 : ((((1 : Int) * (v 124)) * ((v 24) - (29 : Int))) * (v 79)) = 0
  h9234 : ((((1 : Int) * (v 124)) * ((v 24) - (32 : Int))) * (v 80)) = 0
  h9236 : ((((1 : Int) * (v 124)) * ((v 24) - (35 : Int))) * (v 81)) = 0
  h9238 : ((((1 : Int) * (v 124)) * ((v 24) - (36 : Int))) * (v 82)) = 0
  h9240 : ((((1 : Int) * (v 124)) * ((v 24) - (37 : Int))) * (v 83)) = 0
  h9242 : ((((1 : Int) * (v 124)) * ((v 24) - (38 : Int))) * (v 84)) = 0
  h9244 : ((((1 : Int) * (v 124)) * ((v 24) - (39 : Int))) * (v 85)) = 0
  h9246 : ((((1 : Int) * (v 124)) * ((v 24) - (40 : Int))) * (v 86)) = 0
  h9248 : ((((1 : Int) * (v 124)) * ((v 24) - (41 : Int))) * (v 87)) = 0
  h9250 : ((((1 : Int) * (v 124)) * ((v 24) - (42 : Int))) * (v 88)) = 0
  h9252 : ((((1 : Int) * (v 124)) * ((v 24) - (43 : Int))) * (v 89)) = 0
  h9254 : ((((1 : Int) * (v 124)) * ((v 24) - (44 : Int))) * (v 90)) = 0
  h9256 : ((((1 : Int) * (v 124)) * ((v 24) - (45 : Int))) * (v 91)) = 0
  h9258 : ((((1 : Int) * (v 124)) * ((v 24) - (46 : Int))) * (v 92)) = 0
  h9260 : ((((1 : Int) * (v 124)) * ((v 24) - (47 : Int))) * (v 93)) = 0
  h9262 : ((((1 : Int) * (v 124)) * ((v 24) - (48 : Int))) * (v 94)) = 0
  h9264 : ((((1 : Int) * (v 124)) * ((v 24) - (49 : Int))) * (v 95)) = 0
  h9266 : ((((1 : Int) * (v 124)) * ((v 24) - (50 : Int))) * (v 96)) = 0
  h9268 : ((((1 : Int) * (v 124)) * ((v 24) - (51 : Int))) * (v 97)) = 0
  h9270 : ((((1 : Int) * (v 124)) * ((v 24) - (52 : Int))) * (v 98)) = 0
  h9272 : ((((1 : Int) * (v 124)) * ((v 24) - (57 : Int))) * (v 99)) = 0
  h9274 : ((((1 : Int) * (v 124)) * ((v 24) - (58 : Int))) * (v 100)) = 0
  h9276 : ((((1 : Int) * (v 124)) * ((v 24) - (66 : Int))) * (v 101)) = 0
  h9278 : ((((1 : Int) * (v 124)) * ((v 24) - (67 : Int))) * (v 102)) = 0
  h9280 : ((((1 : Int) * (v 124)) * ((v 24) - (68 : Int))) * (v 103)) = 0
  h9282 : (((1 : Int) * (v 124)) * ((1 : Int) - (v 104))) = 0
  h9283 : (((1 : Int) * (v 124)) * ((((((((((((((((((((((((((((v 105) - (v 104)) - (((1 : Int) * (-1 : Int)) * (v 78))) - (((1 : Int) * (-1 : Int)) * (v 79))) - (((1 : Int) * (-1 : Int)) * (v 80))) - (((1 : Int) * (-1 : Int)) * (v 81))) - (((1 : Int) * (-1 : Int)) * (v 82))) - (((1 : Int) * (-1 : Int)) * (v 83))) - (((1 : Int) * (-1 : Int)) * (v 84))) - (((1 : Int) * (-1 : Int)) * (v 85))) - (((1 : Int) * (-1 : Int)) * (v 86))) - (((1 : Int) * (-1 : Int)) * (v 87))) - (((1 : Int) * (-1 : Int)) * (v 88))) - (((1 : Int) * (-1 : Int)) * (v 89))) - (((1 : Int) * (-1 : Int)) * (v 90))) - (((1 : Int) * (-1 : Int)) * (v 91))) - (((1 : Int) * (-1 : Int)) * (v 92))) - (((1 : Int) * (-1 : Int)) * (v 93))) - (((1 : Int) * (-1 : Int)) * (v 94))) - (((1 : Int) * (-1 : Int)) * (v 95))) - (((1 : Int) * (-1 : Int)) * (v 96))) - (((1 : Int) * (-1 : Int)) * (v 97))) - (((1 : Int) * (-1 : Int)) * (v 98))) - (((1 : Int) * (-1 : Int)) * (v 99))) - (((1 : Int) * (-1 : Int)) * (v 100))) - (((1 : Int) * (-1 : Int)) * (v 101))) - (((1 : Int) * (-1 : Int)) * (v 102))) - (((1 : Int) * (-1 : Int)) * (v 103)))) = 0
  h9284 : ((((1 : Int) * (v 124)) * (v 105)) * (((((0 : Int) + (v 23)) + (((1 : Int) * (65536 : Int)) * (v 47))) - (v 13)) - (4 : Int))) = 0
  h9285 : ((((1 : Int) * (v 124)) * (v 105)) * (((((0 : Int) + (v 22)) + (((1 : Int) * (65536 : Int)) * (v 59))) - (v 12)) - (v 47))) = 0
  h9286 : ((((1 : Int) * (v 124)) * (v 105)) * (((((0 : Int) + (v 21)) + (((1 : Int) * (65536 : Int)) * (v 62))) - (v 11)) - (v 59))) = 0
  h9287 : ((((1 : Int) * (v 124)) * (v 105)) * (((v 20) - (v 10)) - (v 62))) = 0
  h9288 : ((((1 : Int) * (v 124)) * (v 105)) * ((v 16) - (v 77))) = 0
  h9289 : ((((1 : Int) * (v 124)) * (v 105)) * ((v 15) - (v 76))) = 0
  h9290 : ((((1 : Int) * (v 124)) * (v 105)) * ((v 14) - (v 75))) = 0
  h9291 : ((((1 : Int) * (v 124)) * (v 105)) * ((v 19) - (v 5))) = 0
  h9292 : ((((1 : Int) * (v 124)) * (v 105)) * ((v 18) - (v 4))) = 0
  h9293 : ((((1 : Int) * (v 124)) * (v 105)) * ((v 17) - (v 3))) = 0
  h9294 : (((1 : Int) * (v 124)) * ((((0 : Int) + (((1 : Int) * (v 78)) * (v 57))) + (((1 : Int) * (v 78)) * (v 56))) + (((1 : Int) * (v 78)) * (v 55)))) = 0
  h9295 : ((((1 : Int) * (v 124)) * (v 79)) * ((((v 48) - (v 35)) - (((1 : Int) * (-1 : Int)) * (v 39))) - (((1 : Int) * (65536 : Int)) * (v 59)))) = 0
  h9296 : ((((1 : Int) * (v 124)) * (v 79)) * (((((v 43) - (v 34)) - (((1 : Int) * (-1 : Int)) * (v 38))) - (((1 : Int) * (-1 : Int)) * (v 59))) - (((1 : Int) * (65536 : Int)) * (v 62)))) = 0
  h9297 : ((((1 : Int) * (v 124)) * (v 79)) * (((((v 42) - (v 33)) - (((1 : Int) * (-1 : Int)) * (v 37))) - (((1 : Int) * (-1 : Int)) * (v 62))) - (((1 : Int) * (65536 : Int)) * (v 110)))) = 0
  h9298 : ((((1 : Int) * (v 124)) * (v 79)) * (((((v 41) - (v 32)) - (((1 : Int) * (-1 : Int)) * (v 36))) - (((1 : Int) * (-1 : Int)) * (v 110))) - (((1 : Int) * (65536 : Int)) * (v 111)))) = 0
  h9299 : ((((1 : Int) * (v 124)) * (v 79)) * ((v 47) - (v 111))) = 0
  h9300 : (((1 : Int) * (v 124)) * (((((0 : Int) + ((((1 : Int) * (v 79)) * (v 58)) * ((1 : Int) - (v 47)))) + ((((1 : Int) * (v 79)) * (v 57)) * ((1 : Int) - (v 47)))) + ((((1 : Int) * (v 79)) * (v 56)) * ((1 : Int) - (v 47)))) + ((((1 : Int) * (v 79)) * (v 55)) * ((1 : Int) - (v 47))))) = 0
  h9301 : (((((1 : Int) * (v 124)) * (v 47)) * (v 79)) * ((v 58) - (1 : Int))) = 0
  h9302 : (((1 : Int) * (v 124)) * ((((0 : Int) + ((((1 : Int) * (v 47)) * (v 79)) * (v 57))) + ((((1 : Int) * (v 47)) * (v 79)) * (v 56))) + ((((1 : Int) * (v 47)) * (v 79)) * (v 55)))) = 0
  h9303 : ((((1 : Int) * (v 124)) * (v 80)) * ((((0 : Int) + (v 44)) + (((1 : Int) * (64 : Int)) * (v 112))) - (v 39))) = 0
  h9304 : ((((1 : Int) * (v 124)) * (v 80)) * (((((0 : Int) + (v 43)) + (((1 : Int) * (65536 : Int)) * (v 113))) - (v 112)) - (((1 : Int) * (1024 : Int)) * (v 38)))) = 0
  h9305 : ((((1 : Int) * (v 124)) * (v 80)) * (((((0 : Int) + (v 42)) + (((1 : Int) * (65536 : Int)) * (v 114))) - (v 113)) - (((1 : Int) * (1024 : Int)) * (v 37)))) = 0
  h9306 : ((((1 : Int) * (v 124)) * (v 80)) * (((((0 : Int) + (v 41)) + (((1 : Int) * (65536 : Int)) * (v 115))) - (v 114)) - (((1 : Int) * (1024 : Int)) * (v 36)))) = 0
  h9307 : ((((1 : Int) * (v 124)) * (v 80)) * ((v 40) - (v 115))) = 0
  h9309 : (((((1 : Int) * (v 124)) * ((v 32) - (32768 : Int))) * (v 85)) * ((1 : Int) - (v 47))) = 0
  h9310 : ((((1 : Int) * (v 124)) * ((((0 : Int) + (((1 : Int) * (v 33)) * (v 85))) + (((1 : Int) * (v 34)) * (v 85))) + (((1 : Int) * (v 35)) * (v 85)))) * ((1 : Int) - (v 47))) = 0
  h9312 : ((((1 : Int) * (v 124)) * (((((0 : Int) + ((((1 : Int) * ((65535 : Int) - (v 36))) * (v 85)) * ((1 : Int) - (v 47)))) + ((((1 : Int) * ((65535 : Int) - (v 37))) * (v 85)) * ((1 : Int) - (v 47)))) + ((((1 : Int) * ((65535 : Int) - (v 38))) * (v 85)) * ((1 : Int) - (v 47)))) + ((((1 : Int) * ((65535 : Int) - (v 39))) * (v 85)) * ((1 : Int) - (v 47))))) * ((1 : Int) - (v 59))) = 0
  h9317 : ((((1 : Int) * (v 124)) * (v 89)) * ((v 49) - (v 35))) = 0
  h9318 : ((((1 : Int) * (v 124)) * (v 89)) * ((v 48) - (v 34))) = 0
  h9319 : ((((1 : Int) * (v 124)) * (v 89)) * ((v 43) - (v 33))) = 0
  h9320 : ((((1 : Int) * (v 124)) * (v 89)) * ((v 42) - (v 32))) = 0
  h9321 : ((((1 : Int) * (v 124)) * (v 89)) * ((v 53) - (v 39))) = 0
  h9322 : ((((1 : Int) * (v 124)) * (v 89)) * ((v 52) - (v 38))) = 0
  h9323 : ((((1 : Int) * (v 124)) * (v 89)) * ((v 51) - (v 37))) = 0
  h9324 : ((((1 : Int) * (v 124)) * (v 89)) * ((v 50) - (v 36))) = 0
  h9325 : ((((1 : Int) * (v 124)) * (v 89)) * (((((0 : Int) + (v 54)) + (((1 : Int) * (65536 : Int)) * (v 59))) - (v 49)) - (v 53))) = 0
  h9326 : ((((1 : Int) * (v 124)) * (v 89)) * ((((((0 : Int) + (v 41)) + (((1 : Int) * (65536 : Int)) * (v 62))) - (v 48)) - (v 52)) - (v 59))) = 0
  h9327 : ((((1 : Int) * (v 124)) * (v 89)) * ((v 47) - (v 62))) = 0
  h9328 : ((((1 : Int) * (v 124)) * (v 90)) * ((v 49) - (v 35))) = 0
  h9329 : ((((1 : Int) * (v 124)) * (v 90)) * ((v 48) - (v 34))) = 0
  h9330 : ((((1 : Int) * (v 124)) * (v 90)) * ((v 43) - (v 33))) = 0
  h9331 : ((((1 : Int) * (v 124)) * (v 90)) * ((v 42) - (v 32))) = 0
  h9332 : ((((1 : Int) * (v 124)) * (v 90)) * ((v 53) - (v 39))) = 0
  h9333 : ((((1 : Int) * (v 124)) * (v 90)) * ((v 52) - (v 38))) = 0
  h9334 : ((((1 : Int) * (v 124)) * (v 90)) * ((v 51) - (v 37))) = 0
  h9335 : ((((1 : Int) * (v 124)) * (v 90)) * ((v 50) - (v 36))) = 0
  h9336 : ((((1 : Int) * (v 124)) * (v 90)) * ((1 : Int) - (v 62))) = 0
  h9337 : ((((1 : Int) * (v 124)) * (v 90)) * ((v 61) - (v 49))) = 0
  h9338 : ((((1 : Int) * (v 124)) * (v 90)) * (((((0 : Int) + (v 60)) + (((1 : Int) * (65536 : Int)) * (v 59))) - (v 48)) - (((1 : Int) * (65536 : Int)) * (v 62)))) = 0
  h9339 : ((((1 : Int) * (v 124)) * (v 90)) * ((((v 54) - (v 61)) - (((1 : Int) * (-1 : Int)) * (v 53))) - (((1 : Int) * (65536 : Int)) * (v 110)))) = 0
  h9340 : ((((1 : Int) * (v 124)) * (v 90)) * (((((v 41) - (v 60)) - (((1 : Int) * (-1 : Int)) * (v 52))) - (((1 : Int) * (-1 : Int)) * (v 110))) - (((1 : Int) * (65536 : Int)) * (v 111)))) = 0
  h9341 : ((((1 : Int) * (v 124)) * (v 90)) * (((v 47) - (v 59)) - (((1 : Int) * (-1 : Int)) * (v 111)))) = 0
  h9342 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 49) - (v 35))) = 0
  h9343 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 48) - (v 34))) = 0
  h9344 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 43) - (v 33))) = 0
  h9345 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 42) - (v 32))) = 0
  h9346 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 53) - (v 39))) = 0
  h9347 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 52) - (v 38))) = 0
  h9348 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 51) - (v 37))) = 0
  h9349 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 50) - (v 36))) = 0
  h9350 : ((((1 : Int) * (v 124)) * (v 91)) * ((((0 : Int) + (v 46)) + (((1 : Int) * (32 : Int)) * (v 116))) - (v 53))) = 0
  h9351 : ((((1 : Int) * (v 124)) * (v 91)) * (((((0 : Int) + (v 41)) + (((1 : Int) * (65536 : Int)) * (v 117))) - (v 116)) - (((1 : Int) * (2048 : Int)) * (v 52)))) = 0
  h9352 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 45) - (v 117))) = 0
  h9353 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 60) - (v 65))) = 0
  h9354 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 54) - (v 64))) = 0
  h9355 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 67) - (v 63))) = 0
  h9356 : ((((1 : Int) * (v 124)) * (v 91)) * ((v 66) - (v 61))) = 0
  h9357 : ((((1 : Int) * (v 124)) * (v 92)) * ((v 49) - (v 35))) = 0
  h9358 : ((((1 : Int) * (v 124)) * (v 92)) * ((v 48) - (v 34))) = 0
  h9359 : ((((1 : Int) * (v 124)) * (v 92)) * ((v 43) - (v 33))) = 0
  h9360 : ((((1 : Int) * (v 124)) * (v 92)) * ((v 42) - (v 32))) = 0
  h9361 : ((((1 : Int) * (v 124)) * (v 92)) * ((v 53) - (v 39))) = 0
  h9362 : ((((1 : Int) * (v 124)) * (v 92)) * ((v 52) - (v 38))) = 0
  h9363 : ((((1 : Int) * (v 124)) * (v 92)) * ((v 51) - (v 37))) = 0
  h9364 : ((((1 : Int) * (v 124)) * (v 92)) * ((v 50) - (v 36))) = 0
  h9365 : ((((1 : Int) * (v 124)) * (v 92)) * ((((0 : Int) + (v 46)) + (((1 : Int) * (32 : Int)) * (v 116))) - (v 53))) = 0
  h9366 : ((((1 : Int) * (v 124)) * (v 92)) * (((((0 : Int) + (v 41)) + (((1 : Int) * (65536 : Int)) * (v 117))) - (v 116)) - (((1 : Int) * (2048 : Int)) * (v 52)))) = 0
  h9367 : ((((1 : Int) * (v 124)) * (v 92)) * ((v 45) - (v 117))) = 0
  h9368 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 49) - (v 35))) = 0
  h9369 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 48) - (v 34))) = 0
  h9370 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 43) - (v 33))) = 0
  h9371 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 42) - (v 32))) = 0
  h9372 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 53) - (v 39))) = 0
  h9373 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 52) - (v 38))) = 0
  h9374 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 51) - (v 37))) = 0
  h9375 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 50) - (v 36))) = 0
  h9376 : ((((1 : Int) * (v 124)) * (v 93)) * ((((0 : Int) + (v 46)) + (((1 : Int) * (32 : Int)) * (v 116))) - (v 53))) = 0
  h9377 : ((((1 : Int) * (v 124)) * (v 93)) * (((((0 : Int) + (v 41)) + (((1 : Int) * (65536 : Int)) * (v 117))) - (v 116)) - (((1 : Int) * (2048 : Int)) * (v 52)))) = 0
  h9378 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 45) - (v 117))) = 0
  h9379 : ((((1 : Int) * (v 124)) * (v 93)) * ((v 71) - (v 49))) = 0
  h9380 : ((((1 : Int) * (v 124)) * (v 93)) * ((((0 : Int) + (v 70)) + (((1 : Int) * (32768 : Int)) * (v 47))) - (v 48))) = 0
  h9381 : (((1 : Int) * (v 124)) * (((0 : Int) + ((((1 : Int) * (v 93)) * ((65535 : Int) - (v 67))) * (v 47))) + ((((1 : Int) * (v 93)) * ((65535 : Int) - (v 66))) * (v 47)))) = 0
  h9382 : (((((1 : Int) * (v 124)) * (v 93)) * ((((v 65) - (v 67)) - (((1 : Int) * (-1 : Int)) * (v 49))) - (((1 : Int) * (65536 : Int)) * (v 59)))) * (v 47)) = 0
  h9383 : (((((1 : Int) * (v 124)) * (v 93)) * ((((v 64) - (v 66)) - (((1 : Int) * (-1 : Int)) * (v 48))) - (((1 : Int) * (-1 : Int)) * (v 59)))) * (v 47)) = 0
  h9384 : (((1 : Int) * (v 124)) * (((0 : Int) + ((((1 : Int) * (v 93)) * ((65535 : Int) - (v 69))) * (v 47))) + ((((1 : Int) * (v 93)) * ((65535 : Int) - (v 68))) * (v 47)))) = 0
  h9385 : (((((1 : Int) * (v 124)) * (v 93)) * ((((v 60) - (v 69)) - (((1 : Int) * (-1 : Int)) * (v 63))) - (((1 : Int) * (65536 : Int)) * (v 62)))) * (v 47)) = 0
  h9386 : (((((1 : Int) * (v 124)) * (v 93)) * ((((v 54) - (v 68)) - (((1 : Int) * (-1 : Int)) * (v 61))) - (((1 : Int) * (-1 : Int)) * (v 62)))) * (v 47)) = 0
  h9387 : ((((1 : Int) * (v 124)) * (v 94)) * ((v 49) - (v 35))) = 0
  h9388 : ((((1 : Int) * (v 124)) * (v 94)) * ((v 48) - (v 34))) = 0
  h9389 : ((((1 : Int) * (v 124)) * (v 94)) * ((v 43) - (v 33))) = 0
  h9390 : ((((1 : Int) * (v 124)) * (v 94)) * ((v 42) - (v 32))) = 0
  h9391 : ((((1 : Int) * (v 124)) * (v 94)) * ((v 53) - (v 39))) = 0
  h9392 : ((((1 : Int) * (v 124)) * (v 94)) * ((v 52) - (v 38))) = 0
  h9393 : ((((1 : Int) * (v 124)) * (v 94)) * ((v 51) - (v 37))) = 0
  h9394 : ((((1 : Int) * (v 124)) * (v 94)) * ((v 50) - (v 36))) = 0
  h9395 : ((((1 : Int) * (v 124)) * (v 95)) * ((v 49) - (v 35))) = 0
  h9396 : ((((1 : Int) * (v 124)) * (v 95)) * ((v 48) - (v 34))) = 0
  h9397 : ((((1 : Int) * (v 124)) * (v 95)) * ((v 43) - (v 33))) = 0
  h9398 : ((((1 : Int) * (v 124)) * (v 95)) * ((v 42) - (v 32))) = 0
  h9399 : ((((1 : Int) * (v 124)) * (v 95)) * ((v 53) - (v 39))) = 0
  h9400 : ((((1 : Int) * (v 124)) * (v 95)) * ((v 52) - (v 38))) = 0
  h9401 : ((((1 : Int) * (v 124)) * (v 95)) * ((v 51) - (v 37))) = 0
  h9402 : ((((1 : Int) * (v 124)) * (v 95)) * ((v 50) - (v 36))) = 0
  h9403 : ((((1 : Int) * (v 124)) * (v 96)) * ((v 49) - (v 35))) = 0
  h9404 : ((((1 : Int) * (v 124)) * (v 96)) * ((v 48) - (v 34))) = 0
  h9405 : ((((1 : Int) * (v 124)) * (v 96)) * ((v 43) - (v 33))) = 0
  h9406 : ((((1 : Int) * (v 124)) * (v 96)) * ((v 42) - (v 32))) = 0
  h9407 : ((((1 : Int) * (v 124)) * (v 96)) * ((v 53) - (v 39))) = 0
  h9408 : ((((1 : Int) * (v 124)) * (v 96)) * ((v 52) - (v 38))) = 0
  h9409 : ((((1 : Int) * (v 124)) * (v 96)) * ((v 51) - (v 37))) = 0
  h9410 : ((((1 : Int) * (v 124)) * (v 96)) * ((v 50) - (v 36))) = 0
  h9411 : ((((1 : Int) * (v 124)) * (v 97)) * ((v 49) - (v 35))) = 0
  h9412 : ((((1 : Int) * (v 124)) * (v 97)) * ((v 48) - (v 34))) = 0
  h9413 : ((((1 : Int) * (v 124)) * (v 97)) * ((v 43) - (v 33))) = 0
  h9414 : ((((1 : Int) * (v 124)) * (v 97)) * ((v 42) - (v 32))) = 0
  h9415 : ((((1 : Int) * (v 124)) * (v 97)) * ((v 53) - (v 39))) = 0
  h9416 : ((((1 : Int) * (v 124)) * (v 97)) * ((v 52) - (v 38))) = 0
  h9417 : ((((1 : Int) * (v 124)) * (v 97)) * ((v 51) - (v 37))) = 0
  h9418 : ((((1 : Int) * (v 124)) * (v 97)) * ((v 50) - (v 36))) = 0
  h9419 : ((((1 : Int) * (v 124)) * (v 98)) * ((v 49) - (v 35))) = 0
  h9420 : ((((1 : Int) * (v 124)) * (v 98)) * ((v 48) - (v 34))) = 0
  h9421 : ((((1 : Int) * (v 124)) * (v 98)) * ((v 43) - (v 33))) = 0
  h9422 : ((((1 : Int) * (v 124)) * (v 98)) * ((v 42) - (v 32))) = 0
  h9423 : ((((1 : Int) * (v 124)) * (v 98)) * ((v 53) - (v 39))) = 0
  h9424 : ((((1 : Int) * (v 124)) * (v 98)) * ((v 52) - (v 38))) = 0
  h9425 : ((((1 : Int) * (v 124)) * (v 98)) * ((v 51) - (v 37))) = 0
  h9426 : ((((1 : Int) * (v 124)) * (v 98)) * ((v 50) - (v 36))) = 0
  h9427 : (((1 : Int) * (v 124)) * (((((0 : Int) + (((1 : Int) * (v 99)) * ((65535 : Int) - (v 53)))) + (((1 : Int) * (v 99)) * (v 52))) + (((1 : Int) * (v 99)) * (v 51))) + (((1 : Int) * (v 99)) * (v 50)))) = 0
  h9428 : ((((1 : Int) * (v 124)) * (v 99)) * (((((0 : Int) + (v 23)) + (((1 : Int) * (65536 : Int)) * (v 47))) - (v 13)) - (4 : Int))) = 0
  h9429 : ((((1 : Int) * (v 124)) * (v 99)) * (((((0 : Int) + (v 22)) + (((1 : Int) * (65536 : Int)) * (v 59))) - (v 12)) - (v 47))) = 0
  h9430 : ((((1 : Int) * (v 124)) * (v 99)) * (((((0 : Int) + (v 21)) + (((1 : Int) * (65536 : Int)) * (v 62))) - (v 11)) - (v 59))) = 0
  h9431 : ((((1 : Int) * (v 124)) * (v 99)) * (((v 20) - (v 10)) - (v 62))) = 0
  h9432 : ((((1 : Int) * (v 124)) * (v 99)) * ((v 16) - (v 77))) = 0
  h9433 : ((((1 : Int) * (v 124)) * (v 99)) * ((v 15) - (v 76))) = 0
  h9434 : ((((1 : Int) * (v 124)) * (v 99)) * ((v 14) - (v 75))) = 0
  h9435 : ((((1 : Int) * (v 124)) * (v 99)) * ((v 19) - (v 56))) = 0
  h9436 : ((((1 : Int) * (v 124)) * (v 99)) * ((v 18) - (v 55))) = 0
  h9437 : ((((1 : Int) * (v 124)) * (v 99)) * ((v 17) - (v 54))) = 0
  h9438 : (((1 : Int) * (v 124)) * (((((0 : Int) + (((1 : Int) * (v 100)) * ((65535 : Int) - (v 54)))) + (((1 : Int) * (v 100)) * ((65535 : Int) - (v 53)))) + (((1 : Int) * (v 100)) * (v 52))) + (((1 : Int) * (v 100)) * (v 51)))) = 0
  h9439 : ((((1 : Int) * (v 124)) * (v 100)) * (((((0 : Int) + (v 23)) + (((1 : Int) * (65536 : Int)) * (v 47))) - (v 13)) - (4 : Int))) = 0
  h9440 : ((((1 : Int) * (v 124)) * (v 100)) * (((((0 : Int) + (v 22)) + (((1 : Int) * (65536 : Int)) * (v 59))) - (v 12)) - (v 47))) = 0
  h9441 : ((((1 : Int) * (v 124)) * (v 100)) * (((((0 : Int) + (v 21)) + (((1 : Int) * (65536 : Int)) * (v 62))) - (v 11)) - (v 59))) = 0
  h9442 : ((((1 : Int) * (v 124)) * (v 100)) * (((v 20) - (v 10)) - (v 62))) = 0
  h9443 : ((((1 : Int) * (v 124)) * (v 100)) * ((v 16) - (v 77))) = 0
  h9444 : ((((1 : Int) * (v 124)) * (v 100)) * ((v 15) - (v 76))) = 0
  h9445 : ((((1 : Int) * (v 124)) * (v 100)) * ((v 14) - (v 75))) = 0
  h9446 : ((((1 : Int) * (v 124)) * (v 100)) * ((v 19) - (v 57))) = 0
  h9447 : ((((1 : Int) * (v 124)) * (v 100)) * ((v 18) - (v 56))) = 0
  h9448 : ((((1 : Int) * (v 124)) * (v 100)) * ((v 17) - (v 55))) = 0
  h9449 : ((((1 : Int) * (v 124)) * (v 101)) * ((v 16) - (v 77))) = 0
  h9450 : ((((1 : Int) * (v 124)) * (v 101)) * ((v 15) - (v 76))) = 0
  h9451 : ((((1 : Int) * (v 124)) * (v 101)) * ((v 14) - (v 75))) = 0
  h9452 : ((((1 : Int) * (v 124)) * (v 101)) * ((v 19) - (v 5))) = 0
  h9453 : ((((1 : Int) * (v 124)) * (v 101)) * ((v 18) - (v 4))) = 0
  h9454 : ((((1 : Int) * (v 124)) * (v 101)) * ((v 17) - (v 3))) = 0
  h9455 : ((((1 : Int) * (v 124)) * (v 102)) * ((v 52) - (4 : Int))) = 0
  h9456 : (((1 : Int) * (v 124)) * ((((0 : Int) + (((1 : Int) * (v 102)) * (v 51))) + (((1 : Int) * (v 102)) * (v 50))) + (((1 : Int) * (v 102)) * (v 49)))) = 0
  h9457 : ((((1 : Int) * (v 124)) * (v 102)) * (((((0 : Int) + (v 16)) + (((1 : Int) * (65536 : Int)) * (v 47))) - (v 77)) - (1 : Int))) = 0
  h9458 : ((((1 : Int) * (v 124)) * (v 102)) * (((((0 : Int) + (v 15)) + (((1 : Int) * (65536 : Int)) * (v 59))) - (v 76)) - (v 47))) = 0
  h9459 : ((((1 : Int) * (v 124)) * (v 102)) * (((v 14) - (v 75)) - (v 59))) = 0
  h9460 : ((((1 : Int) * (v 124)) * (v 102)) * ((v 19) - (v 5))) = 0
  h9461 : ((((1 : Int) * (v 124)) * (v 102)) * ((v 18) - (v 4))) = 0
  h9462 : ((((1 : Int) * (v 124)) * (v 102)) * ((v 17) - (v 3))) = 0
  h9463 : ((((1 : Int) * (v 124)) * (v 103)) * ((v 58) - (v 28))) = 0
  h9464 : ((((1 : Int) * (v 124)) * (v 103)) * ((v 57) - (v 27))) = 0
  h9465 : ((((1 : Int) * (v 124)) * (v 103)) * ((v 56) - (v 26))) = 0
  h9466 : ((((1 : Int) * (v 124)) * (v 103)) * ((v 55) - (v 25))) = 0
  h9467 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * (((((0 : Int) + (v 23)) + (((1 : Int) * (65536 : Int)) * (v 119))) - (v 13)) - (4 : Int))) = 0
  h9468 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * (((((0 : Int) + (v 22)) + (((1 : Int) * (65536 : Int)) * (v 120))) - (v 12)) - (v 119))) = 0
  h9469 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * (((((0 : Int) + (v 21)) + (((1 : Int) * (65536 : Int)) * (v 121))) - (v 11)) - (v 120))) = 0
  h9470 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * (((v 20) - (v 10)) - (v 121))) = 0
  h9471 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * (((((0 : Int) + (v 16)) + (((1 : Int) * (65536 : Int)) * (v 122))) - (v 77)) - (1 : Int))) = 0
  h9472 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * (((((0 : Int) + (v 15)) + (((1 : Int) * (65536 : Int)) * (v 123))) - (v 76)) - (v 122))) = 0
  h9473 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * (((v 14) - (v 75)) - (v 123))) = 0
  h9474 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * ((v 19) - (v 5))) = 0
  h9475 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * ((v 18) - (v 4))) = 0
  h9476 : ((((1 : Int) * (v 124)) * (((((((((((((((((((((((0 : Int) + (v 78)) + (v 79)) + (v 80)) + (v 81)) + (v 82)) + (v 83)) + (v 84)) + (v 85)) + (v 86)) + (v 87)) + (v 88)) + (v 89)) + (v 90)) + (v 91)) + (v 92)) + (v 93)) + (v 94)) + (v 95)) + (v 96)) + (v 97)) + (v 98)) + (v 103))) * ((v 17) - (v 3))) = 0
  h9524 : ((((1 : Int) * (v 47)) * (v 47)) - (v 47)) = 0
  h9536 : ((((1 : Int) * (v 59)) * (v 59)) - (v 59)) = 0
  h9539 : ((((1 : Int) * (v 62)) * (v 62)) - (v 62)) = 0
  h9555 : ((((1 : Int) * (v 78)) * (v 78)) - (v 78)) = 0
  h9556 : ((((1 : Int) * (v 79)) * (v 79)) - (v 79)) = 0
  h9557 : ((((1 : Int) * (v 80)) * (v 80)) - (v 80)) = 0
  h9558 : ((((1 : Int) * (v 81)) * (v 81)) - (v 81)) = 0
  h9559 : ((((1 : Int) * (v 82)) * (v 82)) - (v 82)) = 0
  h9560 : ((((1 : Int) * (v 83)) * (v 83)) - (v 83)) = 0
  h9561 : ((((1 : Int) * (v 84)) * (v 84)) - (v 84)) = 0
  h9562 : ((((1 : Int) * (v 85)) * (v 85)) - (v 85)) = 0
  h9563 : ((((1 : Int) * (v 86)) * (v 86)) - (v 86)) = 0
  h9564 : ((((1 : Int) * (v 87)) * (v 87)) - (v 87)) = 0
  h9565 : ((((1 : Int) * (v 88)) * (v 88)) - (v 88)) = 0
  h9566 : ((((1 : Int) * (v 89)) * (v 89)) - (v 89)) = 0
  h9567 : ((((1 : Int) * (v 90)) * (v 90)) - (v 90)) = 0
  h9568 : ((((1 : Int) * (v 91)) * (v 91)) - (v 91)) = 0
  h9569 : ((((1 : Int) * (v 92)) * (v 92)) - (v 92)) = 0
  h9570 : ((((1 : Int) * (v 93)) * (v 93)) - (v 93)) = 0
  h9571 : ((((1 : Int) * (v 94)) * (v 94)) - (v 94)) = 0
  h9572 : ((((1 : Int) * (v 95)) * (v 95)) - (v 95)) = 0
  h9573 : ((((1 : Int) * (v 96)) * (v 96)) - (v 96)) = 0
  h9574 : ((((1 : Int) * (v 97)) * (v 97)) - (v 97)) = 0
  h9575 : ((((1 : Int) * (v 98)) * (v 98)) - (v 98)) = 0
  h9576 : ((((1 : Int) * (v 99)) * (v 99)) - (v 99)) = 0
  h9577 : ((((1 : Int) * (v 100)) * (v 100)) - (v 100)) = 0
  h9578 : ((((1 : Int) * (v 101)) * (v 101)) - (v 101)) = 0
  h9579 : ((((1 : Int) * (v 102)) * (v 102)) - (v 102)) = 0
  h9580 : ((((1 : Int) * (v 103)) * (v 103)) - (v 103)) = 0
  h9581 : ((((1 : Int) * (v 104)) * (v 104)) - (v 104)) = 0
  h9582 : ((((1 : Int) * (v 105)) * (v 105)) - (v 105)) = 0
  h9583 : ((((1 : Int) * (v 106)) * (v 106)) - (v 106)) = 0
  h9584 : ((((1 : Int) * (v 107)) * (v 107)) - (v 107)) = 0
  h9585 : ((((1 : Int) * (v 108)) * (v 108)) - (v 108)) = 0
  h9586 : ((((1 : Int) * (v 109)) * (v 109)) - (v 109)) = 0
  h9587 : ((((1 : Int) * (v 110)) * (v 110)) - (v 110)) = 0
  h9588 : ((((1 : Int) * (v 111)) * (v 111)) - (v 111)) = 0
  h9595 : ((0 : Int) - (v 118)) = 0
  h9596 : ((((1 : Int) * (v 119)) * (v 119)) - (v 119)) = 0
  h9597 : ((((1 : Int) * (v 120)) * (v 120)) - (v 120)) = 0
  h9598 : ((((1 : Int) * (v 121)) * (v 121)) - (v 121)) = 0
  h9599 : ((((1 : Int) * (v 122)) * (v 122)) - (v 122)) = 0
  h9600 : ((((1 : Int) * (v 123)) * (v 123)) - (v 123)) = 0
  h9601 : ((((1 : Int) * (v 124)) * (v 124)) - (v 124)) = 0
  h9676 : (((1 : Int) * (v 124)) * (((((((((((((((((((((((v 150) - (v 78)) - (v 79)) - (v 80)) - (v 81)) - (v 82)) - (v 83)) - (v 84)) - (v 85)) - (v 86)) - (v 87)) - (v 88)) - (v 89)) - (v 90)) - (v 91)) - (v 92)) - (v 93)) - (v 94)) - (v 95)) - (v 96)) - (v 97)) - (v 98)) - (v 103))) = 0
  h9677 : (((1 : Int) * (v 150)) * ((1 : Int) - (v 124))) = 0

theorem integer_equations41 (tables : Tables) (row : Nat)
    (inside : row < (tables 41).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    IntegerEquations41 (fun col => ((readCell tables 41 col row).val : Int)) := by
  have bounded := column_bounds41 tables row inside accepted ranges
  constructor
  · have acceptedExpr := accepted c9224 member9224
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9224 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9224, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9225 member9225
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9225 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9225, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9226 member9226
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9226 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9226, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9227 member9227
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9227 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9227, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9228 member9228
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9228 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9228, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9229 member9229
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9229 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9229, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9230 member9230
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9230 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9230, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9232 member9232
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9232 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9232, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9234 member9234
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9234 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9234, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9236 member9236
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9236 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9236, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9238 member9238
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9238 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9238, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9240 member9240
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9240 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9240, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9242 member9242
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9242 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9242, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9244 member9244
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9244 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9244, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9246 member9246
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9246 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9246, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9248 member9248
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9248 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9248, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9250 member9250
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9250 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9250, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9252 member9252
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9252 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9252, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9254 member9254
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9254 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9254, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9256 member9256
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9256 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9256, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9258 member9258
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9258 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9258, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9260 member9260
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9260 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9260, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9262 member9262
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9262 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9262, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9264 member9264
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9264 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9264, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9266 member9266
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9266 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9266, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9268 member9268
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9268 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9268, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9270 member9270
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9270 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9270, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9272 member9272
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9272 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9272, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9274 member9274
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9274 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9274, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9276 member9276
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9276 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9276, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9278 member9278
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9278 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9278, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9280 member9280
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9280 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9280, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9282 member9282
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9282 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9282, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9283 member9283
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9283 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9283, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9284 member9284
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9284 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9284, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9285 member9285
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9285 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9285, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9286 member9286
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9286 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9286, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9287 member9287
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9287 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9287, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9288 member9288
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9288 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9288, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9289 member9289
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9289 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9289, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9290 member9290
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9290 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9290, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9291 member9291
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9291 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9291, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9292 member9292
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9292 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9292, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9293 member9293
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9293 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9293, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9294 member9294
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9294 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9294, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9295 member9295
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9295 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9295, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9296 member9296
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9296 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9296, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9297 member9297
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9297 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9297, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9298 member9298
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9298 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9298, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9299 member9299
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9299 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9299, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9300 member9300
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9300 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9300, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9301 member9301
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9301 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9301, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9302 member9302
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9302 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9302, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9303 member9303
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9303 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9303, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9304 member9304
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9304 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9304, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9305 member9305
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9305 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9305, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9306 member9306
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9306 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9306, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9307 member9307
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9307 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9307, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9309 member9309
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9309 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9309, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9310 member9310
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9310 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9310, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9312 member9312
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9312 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9312, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9317 member9317
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9317 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9317, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9318 member9318
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9318 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9318, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9319 member9319
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9319 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9319, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9320 member9320
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9320 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9320, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9321 member9321
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9321 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9321, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9322 member9322
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9322 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9322, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9323 member9323
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9323 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9323, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9324 member9324
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9324 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9324, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9325 member9325
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9325 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9325, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9326 member9326
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9326 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9326, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9327 member9327
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9327 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9327, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9328 member9328
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9328 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9328, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9329 member9329
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9329 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9329, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9330 member9330
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9330 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9330, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9331 member9331
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9331 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9331, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9332 member9332
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9332 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9332, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9333 member9333
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9333 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9333, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9334 member9334
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9334 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9334, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9335 member9335
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9335 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9335, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9336 member9336
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9336 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9336, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9337 member9337
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9337 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9337, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9338 member9338
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9338 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9338, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9339 member9339
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9339 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9339, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9340 member9340
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9340 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9340, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9341 member9341
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9341 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9341, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9342 member9342
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9342 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9342, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9343 member9343
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9343 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9343, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9344 member9344
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9344 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9344, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9345 member9345
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9345 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9345, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9346 member9346
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9346 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9346, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9347 member9347
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9347 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9347, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9348 member9348
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9348 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9348, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9349 member9349
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9349 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9349, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9350 member9350
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9350 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9350, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9351 member9351
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9351 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9351, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9352 member9352
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9352 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9352, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9353 member9353
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9353 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9353, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9354 member9354
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9354 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9354, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9355 member9355
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9355 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9355, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9356 member9356
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9356 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9356, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9357 member9357
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9357 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9357, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9358 member9358
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9358 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9358, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9359 member9359
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9359 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9359, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9360 member9360
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9360 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9360, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9361 member9361
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9361 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9361, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9362 member9362
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9362 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9362, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9363 member9363
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9363 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9363, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9364 member9364
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9364 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9364, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9365 member9365
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9365 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9365, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9366 member9366
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9366 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9366, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9367 member9367
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9367 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9367, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9368 member9368
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9368 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9368, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9369 member9369
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9369 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9369, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9370 member9370
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9370 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9370, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9371 member9371
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9371 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9371, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9372 member9372
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9372 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9372, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9373 member9373
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9373 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9373, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9374 member9374
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9374 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9374, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9375 member9375
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9375 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9375, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9376 member9376
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9376 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9376, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9377 member9377
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9377 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9377, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9378 member9378
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9378 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9378, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9379 member9379
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9379 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9379, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9380 member9380
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9380 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9380, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9381 member9381
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9381 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9381, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9382 member9382
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9382 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9382, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9383 member9383
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9383 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9383, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9384 member9384
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9384 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9384, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9385 member9385
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9385 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9385, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9386 member9386
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9386 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9386, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9387 member9387
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9387 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9387, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9388 member9388
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9388 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9388, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9389 member9389
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9389 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9389, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9390 member9390
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9390 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9390, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9391 member9391
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9391 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9391, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9392 member9392
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9392 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9392, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9393 member9393
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9393 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9393, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9394 member9394
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9394 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9394, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9395 member9395
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9395 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9395, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9396 member9396
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9396 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9396, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9397 member9397
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9397 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9397, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9398 member9398
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9398 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9398, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9399 member9399
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9399 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9399, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9400 member9400
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9400 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9400, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9401 member9401
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9401 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9401, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9402 member9402
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9402 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9402, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9403 member9403
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9403 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9403, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9404 member9404
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9404 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9404, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9405 member9405
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9405 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9405, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9406 member9406
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9406 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9406, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9407 member9407
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9407 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9407, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9408 member9408
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9408 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9408, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9409 member9409
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9409 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9409, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9410 member9410
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9410 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9410, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9411 member9411
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9411 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9411, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9412 member9412
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9412 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9412, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9413 member9413
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9413 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9413, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9414 member9414
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9414 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9414, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9415 member9415
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9415 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9415, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9416 member9416
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9416 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9416, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9417 member9417
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9417 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9417, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9418 member9418
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9418 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9418, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9419 member9419
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9419 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9419, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9420 member9420
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9420 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9420, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9421 member9421
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9421 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9421, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9422 member9422
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9422 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9422, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9423 member9423
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9423 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9423, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9424 member9424
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9424 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9424, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9425 member9425
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9425 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9425, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9426 member9426
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9426 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9426, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9427 member9427
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9427 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9427, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9428 member9428
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9428 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9428, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9429 member9429
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9429 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9429, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9430 member9430
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9430 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9430, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9431 member9431
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9431 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9431, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9432 member9432
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9432 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9432, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9433 member9433
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9433 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9433, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9434 member9434
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9434 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9434, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9435 member9435
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9435 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9435, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9436 member9436
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9436 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9436, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9437 member9437
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9437 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9437, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9438 member9438
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9438 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9438, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9439 member9439
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9439 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9439, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9440 member9440
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9440 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9440, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9441 member9441
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9441 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9441, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9442 member9442
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9442 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9442, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9443 member9443
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9443 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9443, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9444 member9444
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9444 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9444, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9445 member9445
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9445 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9445, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9446 member9446
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9446 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9446, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9447 member9447
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9447 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9447, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9448 member9448
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9448 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9448, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9449 member9449
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9449 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9449, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9450 member9450
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9450 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9450, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9451 member9451
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9451 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9451, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9452 member9452
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9452 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9452, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9453 member9453
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9453 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9453, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9454 member9454
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9454 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9454, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9455 member9455
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9455 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9455, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9456 member9456
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9456 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9456, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9457 member9457
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9457 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9457, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9458 member9458
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9458 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9458, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9459 member9459
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9459 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9459, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9460 member9460
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9460 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9460, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9461 member9461
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9461 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9461, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9462 member9462
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9462 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9462, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9463 member9463
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9463 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9463, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9464 member9464
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9464 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9464, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9465 member9465
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9465 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9465, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9466 member9466
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9466 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9466, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9467 member9467
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9467 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9467, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9468 member9468
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9468 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9468, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9469 member9469
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9469 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9469, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9470 member9470
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9470 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9470, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9471 member9471
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9471 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9471, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9472 member9472
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9472 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9472, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9473 member9473
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9473 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9473, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9474 member9474
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9474 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9474, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9475 member9475
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9475 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9475, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9476 member9476
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9476 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9476, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9524 member9524
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9524 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9524, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9536 member9536
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9536 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9536, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9539 member9539
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9539 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9539, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9555 member9555
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9555 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9555, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9556 member9556
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9556 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9556, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9557 member9557
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9557 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9557, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9558 member9558
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9558 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9558, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9559 member9559
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9559 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9559, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9560 member9560
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9560 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9560, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9561 member9561
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9561 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9561, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9562 member9562
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9562 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9562, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9563 member9563
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9563 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9563, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9564 member9564
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9564 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9564, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9565 member9565
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9565 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9565, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9566 member9566
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9566 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9566, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9567 member9567
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9567 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9567, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9568 member9568
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9568 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9568, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9569 member9569
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9569 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9569, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9570 member9570
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9570 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9570, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9571 member9571
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9571 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9571, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9572 member9572
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9572 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9572, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9573 member9573
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9573 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9573, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9574 member9574
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9574 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9574, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9575 member9575
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9575 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9575, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9576 member9576
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9576 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9576, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9577 member9577
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9577 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9577, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9578 member9578
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9578 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9578, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9579 member9579
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9579 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9579, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9580 member9580
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9580 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9580, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9581 member9581
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9581 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9581, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9582 member9582
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9582 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9582, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9583 member9583
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9583 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9583, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9584 member9584
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9584 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9584, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9585 member9585
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9585 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9585, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9586 member9586
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9586 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9586, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9587 member9587
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9587 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9587, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9588 member9588
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9588 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9588, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9595 member9595
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9595 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9595, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9596 member9596
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9596 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9596, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9597 member9597
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9597 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9597, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9598 member9598
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9598 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9598, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9599 member9599
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9599 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9599, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9600 member9600
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9600 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9600, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9601 member9601
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9601 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9601, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9676 member9676
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9676 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9676, Expr.evalInteger, integerConstant, fieldModulus] using lifted
  · have acceptedExpr := accepted c9677 member9677
    have fieldZero := congrArg (fun value : Nat => (value : K))
      (acceptedExpr row (by simp [Expr.bounds]) (by simpa [Expr.bounds] using inside))
    have lifted := Expr.lift_row_zero
      (match c9677 with | .vanishing _ _ expr => expr | _ => .constant 0)
      tables 41 row columns41 bounded (by decide)
      (by decide) (by decide) (by simpa only [Expr.eval_field_bridge, Nat.cast_zero] using fieldZero)
    simpa [c9677, Expr.evalInteger, integerConstant, fieldModulus] using lifted

end DivRemFV.Instruction
