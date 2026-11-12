module
public import CaptureClosure.Proof.TermWireLeaves

@[expose] public section
namespace Perennial
namespace divremfv.internal.airdata.SourceCapture

theorem zigzag_word_value (shift : w64) :
    (zigzagWord shift).toNat = DivRemFV.CaptureSyntax.encodeInt (sint.Z shift) := by
  unfold zigzagWord DivRemFV.CaptureSyntax.encodeInt
  by_cases negative : sint.Z shift < 0
  · rw [if_pos negative]
    have mask : BitVec.sshiftRight' shift (W64 63) = W64 (-1) := by
      apply BitVec.eq_of_toInt_eq
      simp only [BitVec.sshiftRight_eq',show (W64 63).toNat = 63 from rfl,
        BitVec.toInt_sshiftRight,Int.shiftRight_eq_div_pow]
      word
    rw [mask,show W64 (-1) = BitVec.allOnes 64 by word,BitVec.xor_allOnes,BitVec.toNat_not]
    word
  · rw [if_neg negative]
    have mask : BitVec.sshiftRight' shift (W64 63) = W64 0 := by
      apply BitVec.eq_of_toInt_eq
      simp only [BitVec.sshiftRight_eq',show (W64 63).toNat = 63 from rfl,
        BitVec.toInt_sshiftRight,Int.shiftRight_eq_div_pow]
      word
    rw [mask,show W64 0 = (0#64) by word,BitVec.xor_zero]
    word

#print axioms zigzag_word_value
end divremfv.internal.airdata.SourceCapture
end Perennial
