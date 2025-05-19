import Mathlib

/-! ### Lemmas to tag @[cancel] -/

#check lt_of_add_lt_add_right
#check lt_of_mul_lt_mul_left

/-! ### Tests -/

example {a b x y : ℝ} (h : 0 ≤ a) (h : a * x + b < a * y + b) : True := by
  apply lt_of_add_lt_add_right at h
  replace h := lt_of_mul_lt_mul_left h (by positivity)
  trivial
