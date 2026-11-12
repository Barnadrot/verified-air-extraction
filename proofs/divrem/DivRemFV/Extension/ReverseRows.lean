import DivRemFV.Extension.IntegerRows

set_option maxRecDepth 4096

namespace DivRemFV.Extension

theorem integer_to_field67 (v : Nat → Nat)
    (h : IntegerEquations67 (fun col => (v col : Int)))
    : Equations67 (fun col => (v col : K)) := by
  have minusOne : (2130706432 : K) = -1 := by decide
  constructor
  · have cast := congrArg (fun value : Int => (value : K)) h.h12204
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h12205
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h12206
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h12207
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h12208
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h12209
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h12210
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h12211
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h12218
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast
  · have cast := congrArg (fun value : Int => (value : K)) h.h12221
    simpa only [minusOne, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_neg,
      Int.cast_natCast, Int.cast_ofNat, Int.cast_zero, Int.cast_one] using cast

end DivRemFV.Extension
