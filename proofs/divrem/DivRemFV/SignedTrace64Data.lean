import DivRemFV.SignedWitness64

namespace DivRemFV
open Generated

def signed64Q (a b : Nat) := unsignedQ 64 (magnitudeNat 64 a) (magnitudeNat 64 b)
def signed64R (a b : Nat) := unsignedR (magnitudeNat 64 a) (magnitudeNat 64 b)

def signed64Rows (a b : Nat) : Nat → Array NatRow := fun mid =>
  match mid with
  | 55 => #[absolute64Row a,absolute64Row b]
  | 61 => #[unsigned64Row (magnitudeNat 64 a) (magnitudeNat 64 b)]
  | 62 => #[⟨47,signed64Witness a b (signed64Q a b) (signed64R a b),signed64_witness_outside _ _ _ _⟩]
  | 65 => #[negation64Row (signed64Q a b),negation64Row (signed64R a b)]
  | _ => #[]

def signed64Tables (a b : Nat) := witnessTables (signed64Rows a b)

theorem magnitude64_bound (a : Nat) (cap : a < 18446744073709551616) : magnitudeNat 64 a < 18446744073709551616 := by
  unfold magnitudeNat
  norm_num only
  split <;> omega

theorem signed64Q_bound (a b : Nat) (cap : a < 18446744073709551616) : signed64Q a b < 18446744073709551616 :=
  unsignedQ_bound 64 _ _ (magnitude64_bound a cap)

theorem signed64R_bound (a b : Nat) (ab : a < 18446744073709551616) (bb : b < 18446744073709551616) :
    signed64R a b < 18446744073709551616 := unsignedR_bound 64 _ _ (magnitude64_bound a ab) (magnitude64_bound b bb)

theorem signed64_read_main (a b col : Nat) :
    readCell (signed64Tables a b) 62 col 0 = scalarOfNat (signed64Witness a b (signed64Q a b) (signed64R a b) col) := by
  exact witnessTables_read _ 62 0 col (by decide) (by simp [signed64Rows])

theorem signed64_read_absA (a b col : Nat) :
    readCell (signed64Tables a b) 55 col 0 = scalarOfNat ((absolute64Row a).values col) := by
  exact witnessTables_read _ 55 0 col (by decide) (by simp [signed64Rows])

theorem signed64_read_absB (a b col : Nat) :
    readCell (signed64Tables a b) 55 col 1 = scalarOfNat ((absolute64Row b).values col) := by
  exact witnessTables_read _ 55 1 col (by decide) (by simp [signed64Rows])

theorem signed64_read_unsigned (a b col : Nat) :
    readCell (signed64Tables a b) 61 col 0 = scalarOfNat ((unsigned64Row (magnitudeNat 64 a) (magnitudeNat 64 b)).values col) := by
  exact witnessTables_read _ 61 0 col (by decide) (by simp [signed64Rows])

theorem signed64_read_negQ (a b col : Nat) :
    readCell (signed64Tables a b) 65 col 0 = scalarOfNat ((negation64Row (signed64Q a b)).values col) := by
  exact witnessTables_read _ 65 0 col (by decide) (by simp [signed64Rows])

theorem signed64_read_negR (a b col : Nat) :
    readCell (signed64Tables a b) 65 col 1 = scalarOfNat ((negation64Row (signed64R a b)).values col) := by
  exact witnessTables_read _ 65 1 col (by decide) (by simp [signed64Rows])

end DivRemFV
