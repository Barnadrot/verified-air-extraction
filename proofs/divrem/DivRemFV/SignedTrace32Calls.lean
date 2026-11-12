import DivRemFV.SignedTrace32Data

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace DivRemFV
open Generated

theorem signed32_call_absA (a b : Nat) (cap : a < 4294967296) : c12114.Holds (signed32Tables a b) := by
  unfold c12114
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed32Tables,witnessTables,signed32Rows] using inside
    omega
  subst row
  refine ⟨0,by simp [signed32Tables,witnessTables,signed32Rows],?_,?_⟩
  · simp [Port.Active,signed32_read_absA,absolute32Row,absolute32Witness,scalarOfNat,fieldModulus]
  · have columns := absolute32_witness_digits a cap
    have high := congrArg Prod.fst columns
    have low := congrArg Prod.snd columns
    dsimp only [digits32,Prod.fst,Prod.snd] at high low
    norm_num only [Port.tuple]
    simp only [List.toList_toArray,List.map_cons,List.map_nil,signed32_read_main,signed32_read_absA]
    change [scalarOfNat (a/65536),scalarOfNat (a%65536),
      scalarOfNat (absolute32Witness (a/65536) (a%65536) 2),scalarOfNat (absolute32Witness (a/65536) (a%65536) 3)] =
      [scalarOfNat (a/65536),scalarOfNat (a%65536),scalarOfNat (magnitudeNat 32 a/65536),scalarOfNat (magnitudeNat 32 a%65536)]
    rw [high,low]

theorem signed32_call_absB (a b : Nat) (cap : b < 4294967296) : c12115.Holds (signed32Tables a b) := by
  unfold c12115
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed32Tables,witnessTables,signed32Rows] using inside
    omega
  subst row
  refine ⟨1,by simp [signed32Tables,witnessTables,signed32Rows],?_,?_⟩
  · simp [Port.Active,signed32_read_absB,absolute32Row,absolute32Witness,scalarOfNat,fieldModulus]
  · have columns := absolute32_witness_digits b cap
    have high := congrArg Prod.fst columns
    have low := congrArg Prod.snd columns
    dsimp only [digits32,Prod.fst,Prod.snd] at high low
    norm_num only [Port.tuple]
    simp only [List.toList_toArray,List.map_cons,List.map_nil,signed32_read_main,signed32_read_absB]
    change [scalarOfNat (b/65536),scalarOfNat (b%65536),
      scalarOfNat (absolute32Witness (b/65536) (b%65536) 2),scalarOfNat (absolute32Witness (b/65536) (b%65536) 3)] =
      [scalarOfNat (b/65536),scalarOfNat (b%65536),scalarOfNat (magnitudeNat 32 b/65536),scalarOfNat (magnitudeNat 32 b%65536)]
    rw [high,low]

theorem signed32_call_unsigned (a b : Nat) : c12116.Holds (signed32Tables a b) := by
  unfold c12116
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed32Tables,witnessTables,signed32Rows] using inside
    omega
  subst row
  refine ⟨0,by simp [signed32Tables,witnessTables,signed32Rows],?_,?_⟩
  · by_cases zero : magnitudeNat 32 b=0 <;>
      simp [Port.Active,signed32_read_unsigned,unsigned32Row,zero,unsigned32ZeroWitness,unsigned32NonzeroWitness,scalarOfNat,fieldModulus]
  · norm_num only [Port.tuple]
    simp only [List.toList_toArray,List.map_cons,List.map_nil,signed32_read_main,signed32_read_unsigned]
    by_cases zero : magnitudeNat 32 b=0 <;>
      simp [unsigned32Row,zero,unsigned32ZeroWitness,unsigned32NonzeroWitness,signed32Witness,signed32Q,signed32R,unsignedQ,unsignedR]

theorem signed32_call_negQ (a b : Nat) (cap : a < 4294967296) : c12119.Holds (signed32Tables a b) := by
  unfold c12119
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed32Tables,witnessTables,signed32Rows] using inside
    omega
  subst row
  have selected : b≠0 ∧ signValue 32 a≠signValue 32 b := by
    by_contra off
    have check := (return_active (signed32Tables a b) 64 24 #[8,9,4,5] 0).1 active
    simp [signed32_read_main,signed32Witness,off,scalarOfNat] at check
  refine ⟨0,by simp [signed32Tables,witnessTables,signed32Rows],?_,?_⟩
  · simp [Port.Active,signed32_read_negQ,negation32Row,negation32Witness,scalarOfNat,fieldModulus]
  · have columns := negation32_witness_digits (signed32Q a b) (signed32Q_bound a b cap)
    have high := congrArg Prod.fst columns
    have low := congrArg Prod.snd columns
    dsimp only [digits32,Prod.fst,Prod.snd] at high low
    norm_num only [Port.tuple]
    simp only [List.toList_toArray,List.map_cons,List.map_nil,signed32_read_main,signed32_read_negQ,
      signed32Witness,if_neg selected.1,if_neg selected.2]
    change [scalarOfNat (signed32Q a b/65536),scalarOfNat (signed32Q a b%65536),
      scalarOfNat (negation32Witness (signed32Q a b/65536) (signed32Q a b%65536) 2),
      scalarOfNat (negation32Witness (signed32Q a b/65536) (signed32Q a b%65536) 3)] =
      [scalarOfNat (signed32Q a b/65536),scalarOfNat (signed32Q a b%65536),
       scalarOfNat (negateNat 32 (signed32Q a b)/65536),scalarOfNat (negateNat 32 (signed32Q a b)%65536)]
    rw [high,low]

theorem signed32_call_negR (a b : Nat) (ab : a < 4294967296) (bb : b < 4294967296) :
    c12121.Holds (signed32Tables a b) := by
  unfold c12121
  apply lookup_rows_complete
  intro row inside active
  have zero : row=0 := by
    have h : row < 1 := by simpa [signed32Tables,witnessTables,signed32Rows] using inside
    omega
  subst row
  have selected : b≠0 ∧ signValue 32 a=1 := by
    by_contra off
    have check := (return_active (signed32Tables a b) 64 25 #[10,11,6,7] 0).1 active
    simp [signed32_read_main,signed32Witness,off,scalarOfNat] at check
  have negative : signValue 32 a≠0 := by rw [selected.2]; decide
  refine ⟨1,by simp [signed32Tables,witnessTables,signed32Rows],?_,?_⟩
  · simp [Port.Active,signed32_read_negR,negation32Row,negation32Witness,scalarOfNat,fieldModulus]
  · have columns := negation32_witness_digits (signed32R a b) (signed32R_bound a b ab bb)
    have high := congrArg Prod.fst columns
    have low := congrArg Prod.snd columns
    dsimp only [digits32,Prod.fst,Prod.snd] at high low
    norm_num only [Port.tuple]
    simp only [List.toList_toArray,List.map_cons,List.map_nil,signed32_read_main,signed32_read_negR,
      signed32Witness,if_neg selected.1,if_neg negative]
    change [scalarOfNat (signed32R a b/65536),scalarOfNat (signed32R a b%65536),
      scalarOfNat (negation32Witness (signed32R a b/65536) (signed32R a b%65536) 2),
      scalarOfNat (negation32Witness (signed32R a b/65536) (signed32R a b%65536) 3)] =
      [scalarOfNat (signed32R a b/65536),scalarOfNat (signed32R a b%65536),
       scalarOfNat (negateNat 32 (signed32R a b)/65536),scalarOfNat (negateNat 32 (signed32R a b)%65536)]
    rw [high,low]

end DivRemFV



