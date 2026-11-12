import DivRemFV.Generated.IntegerRows
import DivRemFV.Unsigned32

set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

def wordInteger (v : Nat → Int) (start : Nat) : Int :=
  281474976710656 * v start + 4294967296 * v (start + 1) +
    65536 * v (start + 2) + v (start + 3)

theorem unsigned64_nonzero_integer (v : Nat → Int)
    (h : IntegerEquations61 v) (nonnegative : ∀ col, 0 ≤ v col)
    (active : v 121 = 1) (nonzero : v 33 = 1) :
    wordInteger v 0 = wordInteger v 4 * wordInteger v 8 + wordInteger v 12 ∧
    wordInteger v 4 = wordInteger v 12 + wordInteger v 16 + 1 := by
  have zeroEquation := h.h11827
  have zero : v 32 = 0 := by clear * - zeroEquation; omega
  have e6 := h.h11731
  have e7 := h.h11732
  have e8 := h.h11733
  have e9 := h.h11734
  have e10 := h.h11735
  have e11 := h.h11736
  have e12 := h.h11737
  have e13 := h.h11738
  have e14 := h.h11739
  have e15 := h.h11740
  have e16 := h.h11741
  have e17 := h.h11742
  have e18 := h.h11743
  have e19 := h.h11744
  have e20 := h.h11745
  have e21 := h.h11746
  have e22 := h.h11747
  have e23 := h.h11748
  have e24 := h.h11749
  have e25 := h.h11750
  have e26 := h.h11751
  have e27 := h.h11752
  have e28 := h.h11753
  have e29 := h.h11754
  have e30 := h.h11755
  have e31 := h.h11756
  have e32 := h.h11757
  have e33 := h.h11758
  have e34 := h.h11759
  have e35 := h.h11760
  have e36 := h.h11761
  have e37 := h.h11762
  have e38 := h.h11763
  have e39 := h.h11764
  have e40 := h.h11765
  have e41 := h.h11766
  have e42 := h.h11767
  have e43 := h.h11768
  have e44 := h.h11769
  have e45 := h.h11770
  have e46 := h.h11771
  have e47 := h.h11772
  have e48 := h.h11773
  have e49 := h.h11774
  have e50 := h.h11775
  have e51 := h.h11776
  have e52 := h.h11777
  have e53 := h.h11778
  have e54 := h.h11779
  have e55 := h.h11780
  have e56 := h.h11781
  have e57 := h.h11782
  have e58 := h.h11783
  have e59 := h.h11784
  have e60 := h.h11785
  have e61 := h.h11786
  have e62 := h.h11787
  have e63 := h.h11788
  have e64 := h.h11789
  have e65 := h.h11790
  have e66 := h.h11791
  have e67 := h.h11792
  have e68 := h.h11793
  have e69 := h.h11794
  simp only [active, nonzero, zero, zero_add, one_mul, mul_one, sub_zero, neg_mul] at e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 e32 e33 e34 e35 e36 e37 e38 e39 e40 e41 e42 e43 e44 e45 e46 e47 e48 e49 e50 e51 e52 e53 e54 e55 e56 e57 e58 e59 e60 e61 e62 e63 e64 e65 e66 e67 e68 e69
  have qsplit : wordInteger v 8 = 1 * v 34 + 32768 * v 42 + 1073741824 * v 43 + 35184372088832 * v 44 + 1152921504606846976 * v 41 := by
    dsimp [wordInteger]
    clear * - e6 e7 e8 e9 e10 e11 e12
    omega
  have bsplit : wordInteger v 4 = 1 * v 45 + 32768 * v 53 + 1073741824 * v 54 + 35184372088832 * v 55 + 1152921504606846976 * v 52 := by
    dsimp [wordInteger]
    clear * - e13 e14 e15 e16 e17 e18 e19
    omega
  have p0 : v 56 + 32768 * v 57 = v 34 * v 45 := sub_eq_zero.mp e20
  have p1 : v 58 + 32768 * v 59 = v 34 * v 53 := sub_eq_zero.mp e21
  have p2 : v 60 + 32768 * v 61 = v 34 * v 54 := sub_eq_zero.mp e22
  have p3 : v 62 + 32768 * v 63 = v 34 * v 55 := sub_eq_zero.mp e23
  have p4 : v 64 + 32768 * v 65 = v 34 * v 52 := sub_eq_zero.mp e24
  have p5 : v 66 + 32768 * v 67 = v 42 * v 45 := sub_eq_zero.mp e25
  have p6 : v 68 + 32768 * v 69 = v 42 * v 53 := sub_eq_zero.mp e26
  have p7 : v 70 + 32768 * v 71 = v 42 * v 54 := sub_eq_zero.mp e27
  have p8 : v 72 + 32768 * v 73 = v 42 * v 55 := sub_eq_zero.mp e28
  have p9 : v 74 + 32768 * v 75 = v 42 * v 52 := sub_eq_zero.mp e29
  have p10 : v 76 + 32768 * v 77 = v 43 * v 45 := sub_eq_zero.mp e30
  have p11 : v 78 + 32768 * v 79 = v 43 * v 53 := sub_eq_zero.mp e31
  have p12 : v 80 + 32768 * v 81 = v 43 * v 54 := sub_eq_zero.mp e32
  have p13 : v 82 + 32768 * v 83 = v 43 * v 55 := sub_eq_zero.mp e33
  have p14 : v 84 + 32768 * v 85 = v 43 * v 52 := sub_eq_zero.mp e34
  have p15 : v 86 + 32768 * v 87 = v 44 * v 45 := sub_eq_zero.mp e35
  have p16 : v 88 + 32768 * v 89 = v 44 * v 53 := sub_eq_zero.mp e36
  have p17 : v 90 + 32768 * v 91 = v 44 * v 54 := sub_eq_zero.mp e37
  have p18 : v 92 + 32768 * v 93 = v 44 * v 55 := sub_eq_zero.mp e38
  have p19 : v 94 + 32768 * v 95 = v 44 * v 52 := sub_eq_zero.mp e39
  have p20 : v 96 + 32768 * v 97 = v 41 * v 45 := sub_eq_zero.mp e40
  have p21 : v 98 + 32768 * v 99 = v 41 * v 53 := sub_eq_zero.mp e41
  have p22 : v 100 + 32768 * v 101 = v 41 * v 54 := sub_eq_zero.mp e42
  have p23 : v 102 + 32768 * v 103 = v 41 * v 55 := sub_eq_zero.mp e43
  have p24 : v 104 = v 41 * v 52 := sub_eq_zero.mp e44
  have signs : 0 ≤ v 65 ∧ 0 ≤ v 73 ∧ 0 ≤ v 74 ∧ 0 ≤ v 81 ∧ 0 ≤ v 82 ∧ 0 ≤ v 89 ∧ 0 ≤ v 90 ∧ 0 ≤ v 97 ∧ 0 ≤ v 98 ∧ 0 ≤ v 75 ∧ 0 ≤ v 83 ∧ 0 ≤ v 84 ∧ 0 ≤ v 91 ∧ 0 ≤ v 92 ∧ 0 ≤ v 99 ∧ 0 ≤ v 100 ∧ 0 ≤ v 85 ∧ 0 ≤ v 93 ∧ 0 ≤ v 94 ∧ 0 ≤ v 101 ∧ 0 ≤ v 102 ∧ 0 ≤ v 95 ∧ 0 ≤ v 103 ∧ 0 ≤ v 104 := ⟨nonnegative 65, nonnegative 73, nonnegative 74, nonnegative 81, nonnegative 82, nonnegative 89, nonnegative 90, nonnegative 97, nonnegative 98, nonnegative 75, nonnegative 83, nonnegative 84, nonnegative 91, nonnegative 92, nonnegative 99, nonnegative 100, nonnegative 85, nonnegative 93, nonnegative 94, nonnegative 101, nonnegative 102, nonnegative 95, nonnegative 103, nonnegative 104⟩
  have zeros : v 65 = 0 ∧ v 73 = 0 ∧ v 74 = 0 ∧ v 81 = 0 ∧ v 82 = 0 ∧ v 89 = 0 ∧ v 90 = 0 ∧ v 97 = 0 ∧ v 98 = 0 ∧ v 75 = 0 ∧ v 83 = 0 ∧ v 84 = 0 ∧ v 91 = 0 ∧ v 92 = 0 ∧ v 99 = 0 ∧ v 100 = 0 ∧ v 85 = 0 ∧ v 93 = 0 ∧ v 94 = 0 ∧ v 101 = 0 ∧ v 102 = 0 ∧ v 95 = 0 ∧ v 103 = 0 ∧ v 104 = 0 := by
    clear * - signs e49
    omega
  rcases zeros with ⟨z65,z73,z74,z81,z82,z89,z90,z97,z98,z75,z83,z84,z91,z92,z99,z100,z85,z93,z94,z101,z102,z95,z103,z104⟩
  have expanded : wordInteger v 8 * wordInteger v 4 =
      1 * (v 56) + 32768 * (v 57 + v 58 + v 66) + 1073741824 * (v 59 + v 60 + v 67 + v 68 + v 76) + 35184372088832 * (v 61 + v 62 + v 69 + v 70 + v 77 + v 78 + v 86) + 1152921504606846976 * (v 63 + v 64 + v 71 + v 72 + v 79 + v 80 + v 87 + v 88 + v 96) := by
    rw [qsplit, bsplit]
    calc
      _ = 1 * (v 34 * v 45) + 32768 * (v 34 * v 53) + 1073741824 * (v 34 * v 54) + 35184372088832 * (v 34 * v 55) + 1152921504606846976 * (v 34 * v 52) + 32768 * (v 42 * v 45) + 1073741824 * (v 42 * v 53) + 35184372088832 * (v 42 * v 54) + 1152921504606846976 * (v 42 * v 55) + 37778931862957161709568 * (v 42 * v 52) + 1073741824 * (v 43 * v 45) + 35184372088832 * (v 43 * v 53) + 1152921504606846976 * (v 43 * v 54) + 37778931862957161709568 * (v 43 * v 55) + 1237940039285380274899124224 * (v 43 * v 52) + 35184372088832 * (v 44 * v 45) + 1152921504606846976 * (v 44 * v 53) + 37778931862957161709568 * (v 44 * v 54) + 1237940039285380274899124224 * (v 44 * v 55) + 40564819207303340847894502572032 * (v 44 * v 52) + 1152921504606846976 * (v 41 * v 45) + 37778931862957161709568 * (v 41 * v 53) + 1237940039285380274899124224 * (v 41 * v 54) + 40564819207303340847894502572032 * (v 41 * v 55) + 1329227995784915872903807060280344576 * (v 41 * v 52) := by ring
      _ = _ := by
        rw [← p0, ← p1, ← p2, ← p3, ← p4, ← p5, ← p6, ← p7, ← p8, ← p9, ← p10, ← p11, ← p12, ← p13, ← p14, ← p15, ← p16, ← p17, ← p18, ← p19, ← p20, ← p21, ← p22, ← p23, ← p24]
        simp only [z65, z73, z74, z81, z82, z89, z90, z97, z98, z75, z83, z84, z91, z92, z99, z100, z85, z93, z94, z101, z102, z95, z103, z104, mul_zero, add_zero, zero_add]
        ring
  have product : wordInteger v 8 * wordInteger v 4 = wordInteger v 20 := by
    dsimp [wordInteger] at expanded ⊢
    linear_combination expanded - 32768 * e45 - 1073741824 * e46 - 35184372088832 * e47 - 1152921504606846976 * e48 - 1 * e50 - 65536 * e51 - 4294967296 * e52 - 281474976710656 * e53
  have added : wordInteger v 0 = wordInteger v 20 + wordInteger v 12 := by
    dsimp [wordInteger]
    linear_combination 1 * e54 + 1 * e58 + 65536 * e55 + 65536 * e59 + 4294967296 * e56 + 4294967296 * e60 + 281474976710656 * e57 + 281474976710656 * e61
  constructor
  · rw [← product] at added
    simpa only [mul_comm] using added
  · dsimp [wordInteger]
    linear_combination 1 * e62 + 1 * e66 + 65536 * e63 + 65536 * e67 + 4294967296 * e64 + 4294967296 * e68 + 281474976710656 * e65 + 281474976710656 * e69

end DivRemFV
