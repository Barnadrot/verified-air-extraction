import DivRemFV.AbsoluteValue
import DivRemFV.RowConstruction
import DivRemFV.Generated.Construction
import DivRemFV.SharedTables

set_option maxRecDepth 4096

namespace DivRemFV
open Generated

def absolute32Witness (high low col : Nat) : Nat :=
  match col with
  | 0 => high
  | 1 => low
  | 2 => if high < 32768 then high else 65535 - high + (if low = 0 then 1 else 0)
  | 3 => if high < 32768 then low else if low = 0 then 0 else 65536 - low
  | 4 => if high < 32768 then 0 else 1
  | 5 => 65535 - high
  | 6 => 65535 - low
  | 7 | 8 => 65535
  | 9 => high % 32768
  | 10 => low
  | 11 => 0
  | 12 => if low = 0 then 1 else 0
  | 13 => 1
  | _ => 0

theorem absolute32_witness_bounds (high low : Nat) (highBound : high < 65536)
    (lowBound : low < 65536) : Bounds56 (absolute32Witness high low) := by
  constructor <;> simp only [absolute32Witness] <;> (try split_ifs) <;> omega

theorem absolute32_witness_integer (high low : Nat) (highBound : high < 65536)
    (lowBound : low < 65536) :
    IntegerEquations56 (fun col => (absolute32Witness high low col : Int)) := by
  by_cases positive : high < 32768 <;> by_cases zero : low = 0 <;>
    constructor <;> norm_num [absolute32Witness, positive, zero] <;> omega

theorem absolute32_witness_field (high low : Nat) (highBound : high < 65536)
    (lowBound : low < 65536) :
    Equations56 (fun col => (absolute32Witness high low col : K)) := by
  have h := absolute32_witness_integer high low highBound lowBound
  have minusOne : (2130706432 : K) = -1 := by decide
  constructor
  · have cast := congrArg (fun value : Int => (value : K)) h.h11195
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11196
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11197
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11198
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11199
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11200
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11201
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11202
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11203
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11208
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11215
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11216
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h11217
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast

def absolute32Tables (high low : Nat) : Tables := fun mid =>
  if mid = 56 then #[rowOfNat (absolute32Witness high low) 14] else fixedRangeTables mid

theorem absolute32_tables_fixed (high low : Nat) : StaticTablesFixed (absolute32Tables high low) := by
  intro mid bits member
  simp only [rangeTablePairs, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl

theorem absolute32_read (high low col : Nat) (inside : col < 14) :
    readCell (absolute32Tables high low) 56 col 0 = scalarOfNat (absolute32Witness high low col) := by
  simpa only [readCell, absolute32Tables, ↓reduceIte, Int.reduceLT, Int.toNat_zero,
    Array.getElem?_singleton, Option.getD_some] using rowOfNat_get (absolute32Witness high low) 14 col inside

theorem absolute32_witness_outside (high low col : Nat) (outside : 14 ≤ col) :
    absolute32Witness high low col = 0 := by
  unfold absolute32Witness
  split <;> omega

theorem absolute32_read_field (high low col : Nat) :
    ((readCell (absolute32Tables high low) 56 col 0).val : K) =
      (absolute32Witness high low col : K) := by
  by_cases inside : col < 14
  · rw [absolute32_read high low col inside]
    simp [scalarOfNat]
  · have outside := absolute32_witness_outside high low col (by omega)
    simp [readCell, absolute32Tables, rowOfNat, inside, outside]

theorem absolute32_read_le (high low col : Nat) :
    (readCell (absolute32Tables high low) 56 col 0).val ≤ absolute32Witness high low col := by
  by_cases inside : col < 14
  · rw [absolute32_read high low col inside]
    exact Nat.mod_le _ _
  · simp [readCell, absolute32Tables, rowOfNat, inside]

theorem absolute32_module_complete (high low : Nat) (highBound : high < 65536)
    (lowBound : low < 65536) :
    ConstraintsHold (absolute32Tables high low) module56Constraints := by
  apply rows56_complete _ (absolute32_tables_fixed high low)
  · intro row inside
    have zero : row = 0 := by
      simp only [absolute32Tables, ↓reduceIte, Array.size_singleton] at inside
      omega
    subst row
    have bounds := absolute32_witness_bounds high low highBound lowBound
    constructor
    · exact lt_of_le_of_lt (absolute32_read_le high low 0) bounds.b0
    · exact lt_of_le_of_lt (absolute32_read_le high low 1) bounds.b1
    · exact lt_of_le_of_lt (absolute32_read_le high low 2) bounds.b2
    · exact lt_of_le_of_lt (absolute32_read_le high low 3) bounds.b3
    · exact lt_of_le_of_lt (absolute32_read_le high low 4) bounds.b4
    · exact lt_of_le_of_lt (absolute32_read_le high low 5) bounds.b5
    · exact lt_of_le_of_lt (absolute32_read_le high low 6) bounds.b6
    · exact lt_of_le_of_lt (absolute32_read_le high low 7) bounds.b7
    · exact lt_of_le_of_lt (absolute32_read_le high low 8) bounds.b8
    · exact lt_of_le_of_lt (absolute32_read_le high low 9) bounds.b9
    · exact lt_of_le_of_lt (absolute32_read_le high low 10) bounds.b10
    · exact lt_of_le_of_lt (absolute32_read_le high low 11) bounds.b11
    · exact lt_of_le_of_lt (absolute32_read_le high low 12) bounds.b12
    · exact lt_of_le_of_lt (absolute32_read_le high low 13) bounds.b13
  · intro row inside
    have zero : row = 0 := by
      simp only [absolute32Tables, ↓reduceIte, Array.size_singleton] at inside
      omega
    subst row
    have equal : (fun col => ((readCell (absolute32Tables high low) 56 col 0).val : K)) =
        (fun col => (absolute32Witness high low col : K)) :=
      funext (absolute32_read_field high low)
    change Equations56 (fun col => ((readCell (absolute32Tables high low) 56 col 0).val : K))
    rw [equal]
    exact absolute32_witness_field high low highBound lowBound

theorem absolute32_slice_complete (high low : Nat) (highBound : high < 65536)
    (lowBound : low < 65536) :
    ConstraintsHold (absolute32Tables high low) constraints := by
  apply constraints_from_modules
  · apply rows55_complete _ (absolute32_tables_fixed high low)
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
  · exact absolute32_module_complete high low highBound lowBound
  · apply rows61_complete _ (absolute32_tables_fixed high low)
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
  · apply rows62_complete _ (absolute32_tables_fixed high low)
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
    · intro message member
      simp [c11984, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
    · intro message member
      simp [c11985, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
    · intro message member
      simp [c11986, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
    · intro message member
      simp [c11989, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
    · intro message member
      simp [c11991, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
  · apply rows63_complete _ (absolute32_tables_fixed high low)
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
  · apply rows64_complete _ (absolute32_tables_fixed high low)
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
    · intro message member
      simp [c12114, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
    · intro message member
      simp [c12115, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
    · intro message member
      simp [c12116, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
    · intro message member
      simp [c12119, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
    · intro message member
      simp [c12121, Constraint.Holds, messages, Port.messages, absolute32Tables, fixedRangeTables] at member
  · apply rows65_complete _ (absolute32_tables_fixed high low)
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
  · apply rows66_complete _ (absolute32_tables_fixed high low)
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside
    · intro row inside
      simp [absolute32Tables, fixedRangeTables] at inside

theorem absolute32_slice_exists (high low : Nat) (highBound : high < 65536)
    (lowBound : low < 65536) :
    ∃ tables : Tables, StaticTablesFixed tables ∧ ConstraintsHold tables constraints ∧
      0 < (tables 56).size ∧ readCell tables 56 13 0 = 1 ∧
      readCell tables 56 0 0 = scalarOfNat high ∧ readCell tables 56 1 0 = scalarOfNat low := by
  refine ⟨absolute32Tables high low, absolute32_tables_fixed high low,
    absolute32_slice_complete high low highBound lowBound, ?_, ?_, ?_, ?_⟩
  · simp [absolute32Tables]
  · rw [absolute32_read high low 13 (by decide)]
    rfl
  · rw [absolute32_read high low 0 (by decide)]
    rfl
  · rw [absolute32_read high low 1 (by decide)]
    rfl

end DivRemFV
