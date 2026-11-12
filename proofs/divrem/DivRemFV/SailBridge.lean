import LeanRV64D.InstsEnd
import DivRemFV.SignedSpec

namespace DivRemFV
open LeanRV64D LeanRV64D.Functions

theorem sail_truncate (width : Nat) (value : Int) :
    to_bits_truncate (l := width) value = BitVec.ofInt width value := by
  apply BitVec.eq_of_toNat_eq
  simp only [to_bits_truncate, Sail.get_slice_int, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofInt, Nat.shiftRight_zero, Nat.zero_add]
  have positive : (0 : Int) ≤ value % ((2 ^ (width + 1) : Nat) : Int) :=
    Int.emod_nonneg _ (by positivity)
  change (value % ((2 ^ (width + 1) : Nat) : Int)).toNat %
    (((2 ^ width : Nat) : Int).toNat) = _
  rw [← Int.toNat_emod positive (by positivity)]
  have divides : ((2 ^ width : Nat) : Int) ∣ ((2 ^ (width + 1) : Nat) : Int) := by
    refine ⟨2, ?_⟩
    push_cast
    rw [pow_succ]
  rw [Int.emod_emod_of_dvd _ divides]

theorem signed_quotient_upper {width : Nat} (a b : BitVec width) :
    a.toInt.tdiv b.toInt ≤ (2 : Int) ^ (width - 1) := by
  have lower := BitVec.le_toInt a
  have upper := BitVec.toInt_lt (x := a)
  have absolute : (a.toInt.natAbs : Int) ≤ (2 : Int) ^ (width - 1) := by omega
  have quotient := Int.natAbs_tdiv_le_natAbs a.toInt b.toInt
  have sign := Int.le_natAbs (a := a.toInt.tdiv b.toInt)
  omega

theorem signed_quotient32_formula (a b : BitVec 32) :
    signedQuotient a b = if b = 0 then BitVec.allOnes 32
      else BitVec.ofInt 32 (a.toInt.tdiv b.toInt) := by
  by_cases zero : b = 0
  · subst b; simp [signedQuotient]
  · have result := congrArg Prod.fst (magnitudeAlgorithm_arch32 a b)
    rw [magnitudeAlgorithm_nonzero a b zero] at result
    simpa only [zero, ↓reduceIte] using result.symm.trans (sdiv_integer a b)

theorem signed_remainder32_formula (a b : BitVec 32) :
    signedRemainder a b = if b = 0 then a
      else BitVec.ofInt 32 (a.toInt.tmod b.toInt) := by
  by_cases zero : b = 0
  · subst b; simp [signedRemainder]
  · have result := congrArg Prod.snd (magnitudeAlgorithm_arch32 a b)
    rw [magnitudeAlgorithm_nonzero a b zero] at result
    simpa only [zero, ↓reduceIte] using result.symm.trans (srem_integer a b)

theorem quotient_clamp32 (value : Int) (bounded : value ≤ 2147483648) :
    BitVec.ofInt 32 (if value ≥ 2147483648 then -2147483648 else value) = BitVec.ofInt 32 value := by
  by_cases overflow : value ≥ 2147483648
  · have equal : value = 2147483648 := by omega
    subst value
    decide
  · simp [overflow]

theorem sail_signed_quotient32 (a b : BitVec 32) :
    to_bits_truncate (l := 32)
      (let q := if b.toInt = 0 then -1 else a.toInt.tdiv b.toInt
       if q ≥ 2147483648 then -2147483648 else q) = signedQuotient a b := by
  rw [sail_truncate]
  have equalZero : b.toInt = 0 ↔ b = 0 := by
    rw [← BitVec.toInt_zero (w := 32), BitVec.toInt_inj]
    rfl
  have bounded : (if b.toInt = 0 then (-1 : Int) else a.toInt.tdiv b.toInt) ≤ 2147483648 := by
    split
    · omega
    · exact signed_quotient_upper a b
  rw [quotient_clamp32 _ bounded, signed_quotient32_formula]
  by_cases zero : b = 0
  · subst b
    change BitVec.ofInt 32 (-1) = BitVec.allOnes 32
    decide
  · simp only [equalZero, zero, ↓reduceIte]

theorem sail_signed_remainder32 (a b : BitVec 32) :
    to_bits_truncate (l := 32) (if b.toInt = 0 then a.toInt else a.toInt.tmod b.toInt) =
      signedRemainder a b := by
  rw [sail_truncate, signed_remainder32_formula]
  have equalZero : b.toInt = 0 ↔ b = 0 := by
    rw [← BitVec.toInt_zero (w := 32), BitVec.toInt_inj]
    rfl
  by_cases zero : b = 0
  · subst b
    simpa using (BitVec.ofInt_toInt (x := a))
  · have integerNonzero : b.toInt ≠ 0 := fun h => zero (equalZero.mp h)
    simp only [integerNonzero, zero, ↓reduceIte]

theorem sail_unsigned_quotient32 (a b : BitVec 32) :
    to_bits_truncate (l := 32) (if (b.toNat : Int) = 0 then -1 else (a.toNat : Int).tdiv b.toNat) =
      (if b = 0 then BitVec.allOnes 32 else a.udiv b) := by
  rw [sail_truncate]
  have equalZero : b.toNat = 0 ↔ b = 0 := by
    rw [← BitVec.toNat_zero (w := 32), BitVec.toNat_inj]
    rfl
  by_cases zero : b = 0
  · subst b
    change BitVec.ofInt 32 (-1) = BitVec.allOnes 32
    decide
  · have integerNonzero : (b.toNat : Int) ≠ 0 := by
      intro h
      apply zero
      exact equalZero.mp (by exact_mod_cast h)
    rw [if_neg integerNonzero, if_neg zero]
    change BitVec.ofNat 32 (a.toNat / b.toNat) = a.udiv b
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.udiv, BitVec.toNat_ofNat] <;>
      exact lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt

theorem sail_unsigned_remainder32 (a b : BitVec 32) :
    to_bits_truncate (l := 32) (if (b.toNat : Int) = 0 then a.toNat else (a.toNat : Int).tmod b.toNat) =
      (if b = 0 then a else a.umod b) := by
  rw [sail_truncate]
  have equalZero : b.toNat = 0 ↔ b = 0 := by
    rw [← BitVec.toNat_zero (w := 32), BitVec.toNat_inj]
    rfl
  by_cases zero : b = 0
  · subst b
    change BitVec.ofNat 32 a.toNat = a
    simpa using (BitVec.ofNat_toNat _ a)
  · have integerNonzero : (b.toNat : Int) ≠ 0 := by
      intro h
      apply zero
      exact equalZero.mp (by exact_mod_cast h)
    rw [if_neg integerNonzero, if_neg zero]
    change BitVec.ofNat 32 (a.toNat % b.toNat) = a.umod b
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.umod, BitVec.toNat_ofNat] <;>
      exact lt_of_le_of_lt (Nat.mod_le _ _) a.isLt

theorem signed_quotient64_formula (a b : BitVec 64) :
    signedQuotient a b = if b = 0 then BitVec.allOnes 64
      else BitVec.ofInt 64 (a.toInt.tdiv b.toInt) := by
  by_cases zero : b = 0
  · subst b; simp [signedQuotient]
  · have result := congrArg Prod.fst (magnitudeAlgorithm_arch64 a b)
    rw [magnitudeAlgorithm_nonzero a b zero] at result
    simpa only [zero, ↓reduceIte] using result.symm.trans (sdiv_integer a b)

theorem signed_remainder64_formula (a b : BitVec 64) :
    signedRemainder a b = if b = 0 then a
      else BitVec.ofInt 64 (a.toInt.tmod b.toInt) := by
  by_cases zero : b = 0
  · subst b; simp [signedRemainder]
  · have result := congrArg Prod.snd (magnitudeAlgorithm_arch64 a b)
    rw [magnitudeAlgorithm_nonzero a b zero] at result
    simpa only [zero, ↓reduceIte] using result.symm.trans (srem_integer a b)

theorem quotient_clamp64 (value : Int) (bounded : value ≤ 9223372036854775808) :
    BitVec.ofInt 64 (if value ≥ 9223372036854775808 then -9223372036854775808 else value) = BitVec.ofInt 64 value := by
  by_cases overflow : value ≥ 9223372036854775808
  · have equal : value = 9223372036854775808 := by omega
    subst value
    decide
  · simp [overflow]

theorem sail_signed_quotient64 (a b : BitVec 64) :
    to_bits_truncate (l := 64)
      (let q := if b.toInt = 0 then -1 else a.toInt.tdiv b.toInt
       if q ≥ 9223372036854775808 then -9223372036854775808 else q) = signedQuotient a b := by
  rw [sail_truncate]
  have equalZero : b.toInt = 0 ↔ b = 0 := by
    rw [← BitVec.toInt_zero (w := 64), BitVec.toInt_inj]
    rfl
  have bounded : (if b.toInt = 0 then (-1 : Int) else a.toInt.tdiv b.toInt) ≤ 9223372036854775808 := by
    split
    · omega
    · exact signed_quotient_upper a b
  rw [quotient_clamp64 _ bounded, signed_quotient64_formula]
  by_cases zero : b = 0
  · subst b
    change BitVec.ofInt 64 (-1) = BitVec.allOnes 64
    decide
  · simp only [equalZero, zero, ↓reduceIte]

theorem sail_signed_remainder64 (a b : BitVec 64) :
    to_bits_truncate (l := 64) (if b.toInt = 0 then a.toInt else a.toInt.tmod b.toInt) =
      signedRemainder a b := by
  rw [sail_truncate, signed_remainder64_formula]
  have equalZero : b.toInt = 0 ↔ b = 0 := by
    rw [← BitVec.toInt_zero (w := 64), BitVec.toInt_inj]
    rfl
  by_cases zero : b = 0
  · subst b
    simpa using (BitVec.ofInt_toInt (x := a))
  · have integerNonzero : b.toInt ≠ 0 := fun h => zero (equalZero.mp h)
    simp only [integerNonzero, zero, ↓reduceIte]

theorem sail_unsigned_quotient64 (a b : BitVec 64) :
    to_bits_truncate (l := 64) (if (b.toNat : Int) = 0 then -1 else (a.toNat : Int).tdiv b.toNat) =
      (if b = 0 then BitVec.allOnes 64 else a.udiv b) := by
  rw [sail_truncate]
  have equalZero : b.toNat = 0 ↔ b = 0 := by
    rw [← BitVec.toNat_zero (w := 64), BitVec.toNat_inj]
    rfl
  by_cases zero : b = 0
  · subst b
    change BitVec.ofInt 64 (-1) = BitVec.allOnes 64
    decide
  · have integerNonzero : (b.toNat : Int) ≠ 0 := by
      intro h
      apply zero
      exact equalZero.mp (by exact_mod_cast h)
    rw [if_neg integerNonzero, if_neg zero]
    change BitVec.ofNat 64 (a.toNat / b.toNat) = a.udiv b
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.udiv, BitVec.toNat_ofNat] <;>
      exact lt_of_le_of_lt (Nat.div_le_self _ _) a.isLt

theorem sail_unsigned_remainder64 (a b : BitVec 64) :
    to_bits_truncate (l := 64) (if (b.toNat : Int) = 0 then a.toNat else (a.toNat : Int).tmod b.toNat) =
      (if b = 0 then a else a.umod b) := by
  rw [sail_truncate]
  have equalZero : b.toNat = 0 ↔ b = 0 := by
    rw [← BitVec.toNat_zero (w := 64), BitVec.toNat_inj]
    rfl
  by_cases zero : b = 0
  · subst b
    change BitVec.ofNat 64 a.toNat = a
    simpa using (BitVec.ofNat_toNat _ a)
  · have integerNonzero : (b.toNat : Int) ≠ 0 := by
      intro h
      apply zero
      exact equalZero.mp (by exact_mod_cast h)
    rw [if_neg integerNonzero, if_neg zero]
    change BitVec.ofNat 64 (a.toNat % b.toNat) = a.umod b
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.umod, BitVec.toNat_ofNat] <;>
      exact lt_of_le_of_lt (Nat.mod_le _ _) a.isLt

def sailResultStep (op : Operation) (rs2 rs1 rd : regidx) : SailM ExecutionResult := do
  let a ← rX_bits rs1
  let b ← rX_bits rs2
  wX_bits rd (isaResult op a b)
  pure RETIRE_SUCCESS

theorem sail_DIV_signed (rs2 rs1 rd : regidx) :
    execute_DIV rs2 rs1 rd false = sailResultStep .div rs2 rs1 rd := by
  simp only [execute_DIV, sailResultStep, isaResult, Bool.false_eq_true, ↓reduceIte,
    Functions.not, Bool.not_false, Bool.true_and, beq_iff_eq, decide_eq_true_eq, Functions.xlen]
  norm_num only
  congr 1
  funext a
  congr 1
  funext b
  change (do
    wX_bits rd (to_bits_truncate (l := 64)
      (let q := if b.toInt = 0 then -1 else a.toInt.tdiv b.toInt
       if q ≥ 9223372036854775808 then -9223372036854775808 else q))
    pure RETIRE_SUCCESS) = _
  rw [sail_signed_quotient64]


theorem sail_DIV_unsigned (rs2 rs1 rd : regidx) :
    execute_DIV rs2 rs1 rd true = sailResultStep .divu rs2 rs1 rd := by
  simp only [execute_DIV, sailResultStep, isaResult, Bool.false_eq_true, ↓reduceIte,
    Functions.not, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, beq_iff_eq,
    decide_eq_true_eq, Functions.xlen, Sail.BitVec.toNatInt, bind_assoc, pure_bind]
  norm_num only
  congr 1
  funext a
  congr 1
  funext b
  change (do
    wX_bits rd (to_bits_truncate (l := 64) (if (b.toNat : Int) = 0 then -1 else (a.toNat : Int).tdiv (b.toNat : Int)))
    pure RETIRE_SUCCESS) = _
  rw [sail_unsigned_quotient64]

theorem sail_REM_signed (rs2 rs1 rd : regidx) :
    execute_REM rs2 rs1 rd false = sailResultStep .rem rs2 rs1 rd := by
  simp only [execute_REM, sailResultStep, isaResult, Bool.false_eq_true, ↓reduceIte,
    Functions.not, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, beq_iff_eq,
    decide_eq_true_eq, Functions.xlen, Sail.BitVec.toNatInt, bind_assoc, pure_bind]
  norm_num only
  congr 1
  funext a
  congr 1
  funext b
  change (do
    wX_bits rd (to_bits_truncate (l := 64) (if b.toInt = 0 then a.toInt else a.toInt.tmod b.toInt))
    pure RETIRE_SUCCESS) = _
  rw [sail_signed_remainder64]

theorem sail_REM_unsigned (rs2 rs1 rd : regidx) :
    execute_REM rs2 rs1 rd true = sailResultStep .remu rs2 rs1 rd := by
  simp only [execute_REM, sailResultStep, isaResult, Bool.false_eq_true, ↓reduceIte,
    Functions.not, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, beq_iff_eq,
    decide_eq_true_eq, Functions.xlen, Sail.BitVec.toNatInt, bind_assoc, pure_bind]
  norm_num only
  congr 1
  funext a
  congr 1
  funext b
  change (do
    wX_bits rd (to_bits_truncate (l := 64) (if (b.toNat : Int) = 0 then (a.toNat : Int) else (a.toNat : Int).tmod (b.toNat : Int)))
    pure RETIRE_SUCCESS) = _
  rw [sail_unsigned_remainder64]

theorem sail_DIVW_signed (rs2 rs1 rd : regidx) :
    execute_DIVW rs2 rs1 rd false = sailResultStep .divw rs2 rs1 rd := by
  simp only [execute_DIVW, sailResultStep, isaResult, Bool.false_eq_true, ↓reduceIte,
    Functions.not, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, beq_iff_eq,
    decide_eq_true_eq, Functions.xlen, Sail.BitVec.toNatInt, bind_assoc, pure_bind]
  norm_num only
  congr 1
  funext a
  congr 1
  funext b
  change (do
    wX_bits rd ((to_bits_truncate (l := 32) (let q := if (b.setWidth 32).toInt = 0 then -1 else (a.setWidth 32).toInt.tdiv (b.setWidth 32).toInt
       if q ≥ 2147483648 then -2147483648 else q)).signExtend 64)
    pure RETIRE_SUCCESS) = _
  rw [sail_signed_quotient32]

theorem sail_DIVW_unsigned (rs2 rs1 rd : regidx) :
    execute_DIVW rs2 rs1 rd true = sailResultStep .divuw rs2 rs1 rd := by
  simp only [execute_DIVW, sailResultStep, isaResult, Bool.false_eq_true, ↓reduceIte,
    Functions.not, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, beq_iff_eq,
    decide_eq_true_eq, Functions.xlen, Sail.BitVec.toNatInt, bind_assoc, pure_bind]
  norm_num only
  congr 1
  funext a
  congr 1
  funext b
  change (do
    wX_bits rd ((to_bits_truncate (l := 32) (if ((b.setWidth 32).toNat : Int) = 0 then -1 else ((a.setWidth 32).toNat : Int).tdiv ((b.setWidth 32).toNat : Int))).signExtend 64)
    pure RETIRE_SUCCESS) = _
  rw [sail_unsigned_quotient32]

theorem sail_REMW_signed (rs2 rs1 rd : regidx) :
    execute_REMW rs2 rs1 rd false = sailResultStep .remw rs2 rs1 rd := by
  simp only [execute_REMW, sailResultStep, isaResult, Bool.false_eq_true, ↓reduceIte,
    Functions.not, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, beq_iff_eq,
    decide_eq_true_eq, Functions.xlen, Sail.BitVec.toNatInt, bind_assoc, pure_bind]
  norm_num only
  congr 1
  funext a
  congr 1
  funext b
  change (do
    wX_bits rd ((to_bits_truncate (l := 32) (if (b.setWidth 32).toInt = 0 then (a.setWidth 32).toInt else (a.setWidth 32).toInt.tmod (b.setWidth 32).toInt)).signExtend 64)
    pure RETIRE_SUCCESS) = _
  rw [sail_signed_remainder32]

theorem sail_REMW_unsigned (rs2 rs1 rd : regidx) :
    execute_REMW rs2 rs1 rd true = sailResultStep .remuw rs2 rs1 rd := by
  simp only [execute_REMW, sailResultStep, isaResult, Bool.false_eq_true, ↓reduceIte,
    Functions.not, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and, beq_iff_eq,
    decide_eq_true_eq, Functions.xlen, Sail.BitVec.toNatInt, bind_assoc, pure_bind]
  norm_num only
  congr 1
  funext a
  congr 1
  funext b
  change (do
    wX_bits rd ((to_bits_truncate (l := 32) (if ((b.setWidth 32).toNat : Int) = 0 then ((a.setWidth 32).toNat : Int) else ((a.setWidth 32).toNat : Int).tmod ((b.setWidth 32).toNat : Int))).signExtend 64)
    pure RETIRE_SUCCESS) = _
  rw [sail_unsigned_remainder32]

end DivRemFV
