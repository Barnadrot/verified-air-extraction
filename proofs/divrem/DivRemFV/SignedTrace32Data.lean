import DivRemFV.DivisionNatRows

set_option maxRecDepth 4096

namespace DivRemFV
open Generated

def signed32Q (a b : Nat) := unsignedQ 32 (magnitudeNat 32 a) (magnitudeNat 32 b)
def signed32R (a b : Nat) := unsignedR (magnitudeNat 32 a) (magnitudeNat 32 b)

def signed32Rows (a b : Nat) : Nat → Array NatRow := fun mid =>
  match mid with
  | 56 => #[absolute32Row a,absolute32Row b]
  | 63 => #[unsigned32Row (magnitudeNat 32 a) (magnitudeNat 32 b)]
  | 64 => #[⟨27,signed32Witness a b (signed32Q a b) (signed32R a b),signed32_witness_outside _ _ _ _⟩]
  | 66 => #[negation32Row (signed32Q a b),negation32Row (signed32R a b)]
  | _ => #[]

def signed32Tables (a b : Nat) := witnessTables (signed32Rows a b)

theorem magnitude32_bound (a : Nat) (cap : a < 4294967296) : magnitudeNat 32 a < 4294967296 := by
  unfold magnitudeNat
  norm_num only
  split <;> omega

theorem signed32Q_bound (a b : Nat) (cap : a < 4294967296) : signed32Q a b < 4294967296 :=
  unsignedQ_bound 32 _ _ (magnitude32_bound a cap)

theorem signed32R_bound (a b : Nat) (ab : a < 4294967296) (bb : b < 4294967296) :
    signed32R a b < 4294967296 := unsignedR_bound 32 _ _ (magnitude32_bound a ab) (magnitude32_bound b bb)

theorem signed32_read_main (a b col : Nat) :
    readCell (signed32Tables a b) 64 col 0 = scalarOfNat (signed32Witness a b (signed32Q a b) (signed32R a b) col) := by
  exact witnessTables_read _ 64 0 col (by decide) (by simp [signed32Rows])

theorem signed32_read_absA (a b col : Nat) :
    readCell (signed32Tables a b) 56 col 0 = scalarOfNat ((absolute32Row a).values col) := by
  exact witnessTables_read _ 56 0 col (by decide) (by simp [signed32Rows])

theorem signed32_read_absB (a b col : Nat) :
    readCell (signed32Tables a b) 56 col 1 = scalarOfNat ((absolute32Row b).values col) := by
  exact witnessTables_read _ 56 1 col (by decide) (by simp [signed32Rows])

theorem signed32_read_unsigned (a b col : Nat) :
    readCell (signed32Tables a b) 63 col 0 = scalarOfNat ((unsigned32Row (magnitudeNat 32 a) (magnitudeNat 32 b)).values col) := by
  exact witnessTables_read _ 63 0 col (by decide) (by simp [signed32Rows])

theorem signed32_read_negQ (a b col : Nat) :
    readCell (signed32Tables a b) 66 col 0 = scalarOfNat ((negation32Row (signed32Q a b)).values col) := by
  exact witnessTables_read _ 66 0 col (by decide) (by simp [signed32Rows])

theorem signed32_read_negR (a b col : Nat) :
    readCell (signed32Tables a b) 66 col 1 = scalarOfNat ((negation32Row (signed32R a b)).values col) := by
  exact witnessTables_read _ 66 1 col (by decide) (by simp [signed32Rows])

theorem signed32_table_height (a b : Nat) :
    (signed32Tables a b 64).size = 1 ∧ (signed32Tables a b 63).size = 1 ∧
      (signed32Tables a b 56).size = 2 ∧ (signed32Tables a b 66).size = 2 := by
  simp [signed32Tables,witnessTables,signed32Rows]

end DivRemFV
