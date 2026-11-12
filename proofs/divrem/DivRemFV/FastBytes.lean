import DivRemFV.ByteWire

namespace DivRemFV.ByteWire

def readWordsRev : List UInt8 → List Nat → Option (List Nat)
  | [], acc => some acc.reverse
  | a::b::c::d::e::f::g::h::tail, acc =>
    readWordsRev tail (wordValue a b c d e f g h :: acc)
  | _, _ => none

theorem readWordsRev_eq (bytes : List UInt8) (acc : List Nat) :
    readWordsRev bytes acc = (readWords bytes).map (acc.reverse ++ ·) := by
  fun_induction readWords bytes generalizing acc with
  | case1 => simp [readWordsRev, readWords]
  | case2 a b c d e f g h tail ih =>
    rw [readWordsRev, ih]
    cases parsed : readWords tail <;>
      simp [readWords, parsed, List.reverse_cons, List.append_assoc]
  | case3 => simp_all [readWordsRev, readWords]

def readWordsFast (bytes : List UInt8) : Option (List Nat) := readWordsRev bytes []

theorem readWordsFast_eq (bytes : List UInt8) : readWordsFast bytes = readWords bytes := by
  simp [readWordsFast, readWordsRev_eq]

end DivRemFV.ByteWire
