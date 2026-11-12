import DivRemFV.CapturedData
import DivRemFV.SailBridge

namespace DivRemFV.Statement

abbrev Limbs := Scalar × Scalar × Scalar × Scalar

def limb (value : Nat) : Scalar :=
  ⟨value % 65536, Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)⟩

def enc (word : BitVec 64) : Limbs :=
  (limb (word.toNat / 281474976710656), limb (word.toNat / 4294967296),
    limb (word.toNat / 65536), limb word.toNat)

def quotient (a b : BitVec 64) : BitVec 64 :=
  if b = 0 then BitVec.allOnes 64
  else if a = BitVec.intMin 64 ∧ b = BitVec.allOnes 64 then BitVec.intMin 64
  else BitVec.ofInt 64 (a.toInt.tdiv b.toInt)

def remainder (a b : BitVec 64) : BitVec 64 :=
  if b = 0 then a
  else if a = BitVec.intMin 64 ∧ b = BitVec.allOnes 64 then 0
  else BitVec.ofInt 64 (a.toInt.tmod b.toInt)

theorem quotient_eq_signedQuotient (a b : BitVec 64) :
    quotient a b = DivRemFV.signedQuotient a b := rfl

theorem remainder_eq_signedRemainder (a b : BitVec 64) :
    remainder a b = DivRemFV.signedRemainder a b := rfl

theorem component (a b : BitVec 64) (q r : Limbs) :
    (∃ tables : Tables, StaticTablesFixed tables ∧
      NativeImport.RawConstraintsHold tables CapturedData.rawConstraints ∧
      fourList (enc a) ++ fourList (enc b) ++ fourList q ++ fourList r ∈
        signed64Target.messages tables) ↔
      q = enc (quotient a b) ∧ r = enc (remainder a b) :=
  CapturedData.component_iff a b q r

theorem false_remainder_rejected :
    ¬CapturedData.Accepts (encodeFour 0) (encodeFour 2) (encodeFour 0) (encodeFour 1) := by
  have contract := CapturedData.component_iff (0 : BitVec 64) (2 : BitVec 64)
    (encodeFour 0) (encodeFour 1)
  change CapturedData.Accepts (encodeFour 0) (encodeFour 2) (encodeFour 0) (encodeFour 1) ↔ _ at contract
  rw [contract]
  decide

-- These type checks are mandatory even if the broader library still builds.
example (tables : Tables) (raw : List NativeImport.RawConstraint) :
    ConstraintsHold tables (raw.map NativeImport.RawConstraint.translate) ↔
      NativeImport.RawConstraintsHold tables raw :=
  NativeImport.translate_constraints_holds tables raw

example (raw : List NativeImport.RawConstraint) (expected : List Constraint)
    (bound : Binding.check raw expected = true) (tables : Tables) :
    NativeImport.RawConstraintsHold tables raw ↔ ConstraintsHold tables expected :=
  Binding.check_sound raw expected bound tables

example : signed64Target = ⟨62, some 43, #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]⟩ :=
  signed64Target_shape

end DivRemFV.Statement
