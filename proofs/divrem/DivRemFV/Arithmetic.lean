import DivRemFV.Air

namespace DivRemFV

def limbBase : Nat := 65536

def encode64 (word : BitVec 64) (index : Fin 4) : Nat :=
  word.toNat / limbBase ^ (3 - index.val) % limbBase

theorem encode64_canonical (word : BitVec 64) (index : Fin 4) :
    encode64 word index < limbBase :=
  Nat.mod_lt _ (by decide)

theorem lift_bounded_equality (a b : Nat) (ha : a < fieldModulus) (hb : b < fieldModulus)
    (equal : a % fieldModulus = b % fieldModulus) : a = b := by
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using equal

theorem unsigned_divrem_iff (a b q r : Nat) (positive : 0 < b) :
    (a = b * q + r ∧ r < b) ↔ (q = a / b ∧ r = a % b) := by
  constructor
  · intro h
    have result := (Nat.div_mod_unique positive).2
      (show r + b * q = a ∧ r < b from ⟨by omega, h.2⟩)
    exact ⟨result.1.symm, result.2.symm⟩
  · intro h
    have result := (Nat.div_mod_unique positive).1 ⟨h.1.symm, h.2.symm⟩
    exact ⟨by omega, result.2⟩

theorem unsigned_hint_iff (a b q r : Nat) (positive : 0 < b) :
    (∃ auxiliary : Nat, a = b * q + r ∧ b = r + auxiliary + 1) ↔
      (q = a / b ∧ r = a % b) := by
  constructor
  · rintro ⟨auxiliary, identity, bound⟩
    exact (unsigned_divrem_iff a b q r positive).1 ⟨identity, by omega⟩
  · intro result
    obtain ⟨identity, bound⟩ := (unsigned_divrem_iff a b q r positive).2 result
    exact ⟨b - r - 1, identity, by omega⟩

#print axioms encode64_canonical
#print axioms lift_bounded_equality
#print axioms unsigned_divrem_iff
#print axioms unsigned_hint_iff

end DivRemFV
