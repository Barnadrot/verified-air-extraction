import DivRemFV.SignedContract64

namespace DivRemFV
open Generated

abbrev Limbs64 := Scalar × Scalar × Scalar × Scalar

def decodeFour (v : Limbs64) : BitVec 64 :=
  BitVec.ofNat 64 (281474976710656*v.1.val + 4294967296*v.2.1.val +
    65536*v.2.2.1.val + v.2.2.2.val)

theorem four_canonical_of_bounds (a b c d : Scalar)
    (ha : a.val < 65536) (hb : b.val < 65536)
    (hc : c.val < 65536) (hd : d.val < 65536) :
    (a,b,c,d) = encodeFour (decodeFour (a,b,c,d)).toNat := by
  have cap : 281474976710656*a.val + 4294967296*b.val +
      65536*c.val + d.val < 2^64 := by omega
  simpa only [decodeFour, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cap] using
    four_limbs a b c d ha hb hc hd

/-- Input canonicality follows from helper constraints, not a caller premise. -/
theorem signed64_inputs_canonical (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) :
    readFour tables 62 0 row = encodeFour (decodeFour (readFour tables 62 0 row)).toNat ∧
    readFour tables 62 4 row = encodeFour (decodeFour (readFour tables 62 4 row)).toNat := by
  have h := bounds62 tables row inside accepted ranges
  exact ⟨four_canonical_of_bounds _ _ _ _ h.b0 h.b1 h.b2 h.b3,
    four_canonical_of_bounds _ _ _ _ h.b4 h.b5 h.b6 h.b7⟩

theorem signed64_raw_row_sound (tables : Tables) (row : Nat)
    (inside : row < (tables 62).size) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (active : readCell tables 62 43 row ≠ 0) :
    let a := decodeFour (readFour tables 62 0 row)
    let b := decodeFour (readFour tables 62 4 row)
    readFour tables 62 0 row = encodeFour a.toNat ∧
    readFour tables 62 4 row = encodeFour b.toNat ∧
    readFour tables 62 8 row = encodeFour (signedQuotient a b).toNat ∧
    readFour tables 62 12 row = encodeFour (signedRemainder a b).toNat := by
  obtain ⟨ha,hb⟩ := signed64_inputs_canonical tables row inside accepted ranges
  exact ⟨ha,hb,signed64_air_columns_of_ranges tables row inside accepted ranges active _ _
    (readFour_value tables 62 0 row _ (decodeFour _).isLt ha)
    (readFour_value tables 62 4 row _ (decodeFour _).isLt hb)⟩

def Signed64Result (a b q r : Limbs64) : Prop :=
  a = encodeFour (decodeFour a).toNat ∧ b = encodeFour (decodeFour b).toNat ∧
  q = encodeFour (signedQuotient (decodeFour a) (decodeFour b)).toNat ∧
  r = encodeFour (signedRemainder (decodeFour a) (decodeFour b)).toNat

theorem signed64_raw_sound (tables : Tables) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (a b q r : Limbs64)
    (member : fourList a ++ fourList b ++ fourList q ++ fourList r ∈
      signed64Target.messages tables) : Signed64Result a b q r := by
  obtain ⟨row,inside,active,bindings⟩ := (Port.member_iff tables signed64Target _).1 member
  have gate : readCell tables 62 43 row ≠ 0 := by
    rw [signed64Target_shape] at active
    exact (return_active tables 62 43 _ row).1 active
  change row < (tables 62).size at inside
  have columns : readFour tables 62 0 row = a ∧ readFour tables 62 4 row = b ∧
      readFour tables 62 8 row = q ∧ readFour tables 62 12 row = r := by
    simpa [Port.tuple,signed64Target_shape,readFour,fourList,Prod.ext_iff,and_assoc] using bindings
  simpa only [Signed64Result,columns.1,columns.2.1,columns.2.2.1,columns.2.2.2] using
    signed64_raw_row_sound tables row inside accepted ranges gate

def signed64RangeAccepts (a b q r : Limbs64) : Prop :=
  ∃ tables : Tables, StaticRanges tables ∧ ConstraintsHold tables constraints ∧
    fourList a ++ fourList b ++ fourList q ++ fourList r ∈ signed64Target.messages tables

/-- Completeness still uses the canonical witness; soundness needs only ranges. -/
theorem signed64_raw_component_iff (a b q r : Limbs64) :
    signed64RangeAccepts a b q r ↔ Signed64Result a b q r := by
  constructor
  · rintro ⟨tables,ranges,accepted,member⟩
    exact signed64_raw_sound tables accepted ranges a b q r member
  · rintro ⟨ha,hb,hq,hr⟩
    obtain ⟨tables,fixed,accepted,member⟩ :=
      (signed64_component_iff (decodeFour a) (decodeFour b) q r).2 ⟨hq,hr⟩
    refine ⟨tables,fixed_tables_have_ranges tables fixed,accepted,?_⟩
    rw [ha,hb]
    exact member

/-- A raw limb of 65536 cannot pass by wrapping its decoded word to zero. -/
theorem signed64_noncanonical_input_rejected (q r : Limbs64) :
    ¬signed64RangeAccepts (⟨65536,by decide⟩,0,0,0) (encodeFour 2) q r := by
  intro accepted
  have canonical := (signed64_raw_component_iff _ _ q r).1 accepted |>.1
  have first := congrArg (fun v : Limbs64 => v.1.val) canonical
  norm_num [decodeFour,encodeFour,encodeLimb] at first

private def resultPort (start : Nat) : Port :=
  ⟨62,some 43,#[0,1,2,3,4,5,6,7,start,start+1,start+2,start+3]⟩

private theorem result_port_row (tables : Tables) (start : Nat) (a b value : Limbs64)
    (member : fourList a ++ fourList b ++ fourList value ∈ (resultPort start).messages tables) :
    ∃ row, row < (tables 62).size ∧ readCell tables 62 43 row ≠ 0 ∧
      readFour tables 62 0 row = a ∧ readFour tables 62 4 row = b ∧
      readFour tables 62 start row = value := by
  obtain ⟨row,inside,active,bindings⟩ := (Port.member_iff tables (resultPort start) _).1 member
  refine ⟨row,inside,(return_active tables 62 43 _ row).1 active,?_⟩
  simpa [Port.tuple,resultPort,readFour,fourList,Prod.ext_iff,and_assoc] using bindings

theorem signed64_div_port_sound (tables : Tables) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (a b q : Limbs64)
    (member : fourList a ++ fourList b ++ fourList q ∈
      (callTarget incoming9618).messages tables) :
    a = encodeFour (decodeFour a).toNat ∧ b = encodeFour (decodeFour b).toNat ∧
    q = encodeFour (signedQuotient (decodeFour a) (decodeFour b)).toNat := by
  obtain ⟨row,inside,active,ha,hb,hq⟩ := result_port_row tables 8 a b q member
  have result := signed64_raw_row_sound tables row inside accepted ranges active
  exact ⟨by simpa only [ha] using result.1,
    by simpa only [hb] using result.2.1,by simpa only [ha,hb,hq] using result.2.2.1⟩

theorem signed64_rem_port_sound (tables : Tables) (accepted : ConstraintsHold tables constraints)
    (ranges : StaticRanges tables) (a b r : Limbs64)
    (member : fourList a ++ fourList b ++ fourList r ∈
      (callTarget incoming9622).messages tables) :
    a = encodeFour (decodeFour a).toNat ∧ b = encodeFour (decodeFour b).toNat ∧
    r = encodeFour (signedRemainder (decodeFour a) (decodeFour b)).toNat := by
  obtain ⟨row,inside,active,ha,hb,hr⟩ := result_port_row tables 12 a b r member
  have result := signed64_raw_row_sound tables row inside accepted ranges active
  exact ⟨by simpa only [ha] using result.1,
    by simpa only [hb] using result.2.1,by simpa only [ha,hb,hr] using result.2.2.2⟩

end DivRemFV
