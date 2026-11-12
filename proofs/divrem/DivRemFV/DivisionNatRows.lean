import DivRemFV.SignedWitness32
import DivRemFV.UnsignedContract32

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def absolute32Row (a : Nat) : NatRow :=
  ⟨14,absolute32Witness (a/65536) (a%65536),absolute32_witness_outside _ _⟩
def negation32Row (a : Nat) : NatRow :=
  ⟨16,negation32Witness (a/65536) (a%65536),negation32_witness_outside _ _⟩
def absolute64Row (a : Nat) : NatRow :=
  ⟨28,absolute64Witness (digits64 a).1 (digits64 a).2.1 (digits64 a).2.2.1 (digits64 a).2.2.2,
    absolute64_witness_outside _ _ _ _⟩
def negation64Row (a : Nat) : NatRow :=
  ⟨30,negation64Witness (digits64 a).1 (digits64 a).2.1 (digits64 a).2.2.1 (digits64 a).2.2.2,
    negation64_witness_outside _ _ _ _⟩

def unsignedQ (width a b : Nat) : Nat := if b=0 then 2^width-1 else a/b
def unsignedR (a b : Nat) : Nat := if b=0 then a else a%b

def unsigned32Row (a b : Nat) : NatRow :=
  if b=0 then ⟨53,unsigned32ZeroWitness a,unsigned32_zero_outside a⟩ else
    ⟨53,unsigned32NonzeroWitness a b (a/b) (a%b) (b-a%b-1),unsigned32_nonzero_outside _ _ _ _ _⟩
def unsigned64Row (a b : Nat) : NatRow :=
  if b=0 then ⟨123,unsigned64ZeroWitness a,unsigned64_zero_outside a⟩ else
    ⟨123,unsigned64NonzeroWitness a b (a/b) (a%b) (b-a%b-1),unsigned64_nonzero_outside _ _ _ _ _⟩

theorem absolute32_row_valid (a : Nat) (cap : a < 4294967296) :
    Bounds56 (absolute32Row a).values ∧ Equations56 (fun col => ((absolute32Row a).values col : K)) := by
  exact ⟨absolute32_witness_bounds _ _ (by omega) (Nat.mod_lt _ (by decide)),
    absolute32_witness_field _ _ (by omega) (Nat.mod_lt _ (by decide))⟩

theorem negation32_row_valid (a : Nat) (cap : a < 4294967296) :
    Bounds66 (negation32Row a).values ∧ Equations66 (fun col => ((negation32Row a).values col : K)) := by
  exact ⟨negation32_witness_bounds _ _ (by omega) (Nat.mod_lt _ (by decide)),
    negation32_witness_field _ _ (by omega) (Nat.mod_lt _ (by decide))⟩

theorem absolute64_row_valid (a : Nat) (cap : a < 18446744073709551616) :
    Bounds55 (absolute64Row a).values ∧ Equations55 (fun col => ((absolute64Row a).values col : K)) := by
  have hb : (digits64 a).1 < 65536 := by dsimp [digits64]; omega
  have jb : (digits64 a).2.1 < 65536 := Nat.mod_lt _ (by decide)
  have kb : (digits64 a).2.2.1 < 65536 := Nat.mod_lt _ (by decide)
  have lb : (digits64 a).2.2.2 < 65536 := Nat.mod_lt _ (by decide)
  exact ⟨absolute64_witness_bounds _ _ _ _ hb jb kb lb,absolute64_witness_field _ _ _ _ hb jb kb lb⟩

theorem negation64_row_valid (a : Nat) (cap : a < 18446744073709551616) :
    Bounds65 (negation64Row a).values ∧ Equations65 (fun col => ((negation64Row a).values col : K)) := by
  have hb : (digits64 a).1 < 65536 := by dsimp [digits64]; omega
  have jb : (digits64 a).2.1 < 65536 := Nat.mod_lt _ (by decide)
  have kb : (digits64 a).2.2.1 < 65536 := Nat.mod_lt _ (by decide)
  have lb : (digits64 a).2.2.2 < 65536 := Nat.mod_lt _ (by decide)
  exact ⟨negation64_witness_bounds _ _ _ _ hb jb kb lb,negation64_witness_field _ _ _ _ hb jb kb lb⟩

theorem unsignedQ_bound (width a b : Nat) (cap : a < 2^width) : unsignedQ width a b < 2^width := by
  unfold unsignedQ
  split
  · have positive : 0 < 2^width := Nat.two_pow_pos _
    omega
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) cap

theorem unsignedR_bound (width a b : Nat) (aCap : a < 2^width) (bCap : b < 2^width) :
    unsignedR a b < 2^width := by
  unfold unsignedR
  split
  · exact aCap
  · exact lt_trans (Nat.mod_lt _ (by omega)) bCap

theorem unsigned32_row_valid (a b : Nat) (ab : a < 4294967296) (bb : b < 4294967296) :
    Bounds63 (unsigned32Row a b).values ∧ Equations63 (fun col => ((unsigned32Row a b).values col : K)) := by
  by_cases zero : b=0
  · subst b
    exact ⟨unsigned32_zero_witness_bounds a ab,unsigned32_zero_witness_field a⟩
  · have qb : a/b < 4294967296 := lt_of_le_of_lt (Nat.div_le_self _ _) ab
    have small : a%b < b := Nat.mod_lt _ (by omega)
    have rb : a%b < 4294967296 := lt_trans small bb
    have wb : b-a%b-1 < 4294967296 := by omega
    have identity : a = a/b*b + a%b := by
      simpa only [Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div a b).symm
    have bound : b = a%b+(b-a%b-1)+1 := by omega
    simp only [unsigned32Row,zero,↓reduceIte]
    exact ⟨unsigned32_nonzero_witness_bounds _ _ _ _ _ ab bb qb rb wb identity,
      unsigned32_nonzero_witness_field _ _ _ _ _ ab bb qb rb wb identity bound⟩

theorem unsigned64_row_valid (a b : Nat) (ab : a < 18446744073709551616) (bb : b < 18446744073709551616) :
    Bounds61 (unsigned64Row a b).values ∧ Equations61 (fun col => ((unsigned64Row a b).values col : K)) := by
  by_cases zero : b=0
  · subst b
    exact ⟨unsigned64_zero_witness_bounds a ab,unsigned64_zero_witness_field a⟩
  · have qb : a/b < 18446744073709551616 := lt_of_le_of_lt (Nat.div_le_self _ _) ab
    have small : a%b < b := Nat.mod_lt _ (by omega)
    have rb : a%b < 18446744073709551616 := lt_trans small bb
    have wb : b-a%b-1 < 18446744073709551616 := by omega
    have identity : a = a/b*b + a%b := by
      simpa only [Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div a b).symm
    have bound : b = a%b+(b-a%b-1)+1 := by omega
    simp only [unsigned64Row,zero,↓reduceIte]
    exact ⟨unsigned64_nonzero_witness_bounds _ _ _ _ _ ab bb qb rb wb identity,
      unsigned64_nonzero_witness_field _ _ _ _ _ ab bb qb rb wb identity bound⟩

end DivRemFV
