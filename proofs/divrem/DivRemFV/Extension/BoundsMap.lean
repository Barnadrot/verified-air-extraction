import DivRemFV.Extension.Artifact

namespace DivRemFV.Extension

theorem bounds67_of_le (v w : Nat → Nat) (bounds : Bounds67 v)
    (smaller : ∀ col, w col ≤ v col) : Bounds67 w := by
  constructor
  · exact lt_of_le_of_lt (smaller 0) bounds.b0
  · exact lt_of_le_of_lt (smaller 1) bounds.b1
  · exact lt_of_le_of_lt (smaller 2) bounds.b2
  · exact lt_of_le_of_lt (smaller 3) bounds.b3
  · exact lt_of_le_of_lt (smaller 4) bounds.b4
  · exact lt_of_le_of_lt (smaller 5) bounds.b5
  · exact lt_of_le_of_lt (smaller 6) bounds.b6
  · exact lt_of_le_of_lt (smaller 7) bounds.b7
  · exact lt_of_le_of_lt (smaller 8) bounds.b8
  · exact lt_of_le_of_lt (smaller 9) bounds.b9

end DivRemFV.Extension
