import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Util.Qq
import Mathlib.Algebra.Ring.Int.Defs

/-!
## Phase 0: What should the `norm_num` tactic do?

As usual, the first step in writing a tactic is to write by hand some examples of what the tactic
should do.

The `norm_num` tactic is a typical example of the "normalization"/"conv" paradigm for
tactic-writing. We have a notion of "normal form" for a class of expressions.  The tactic changes an
expression to its normal form, justifying this under the hood by producing a proof that the
expression is equal to its normal form.
-/

variable {A : Type*} [Semiring A] (x : A)

/-!
In the case of `norm_num`, the class of expressions is arithmetic expressions involving numerals in
a semiring `A` (or some weaker typeclass, but let's not over-complicate things).  The normal form is
the cast of a single `ℕ` numeral (or `ℤ` or `ℚ`, but let's not over-complicate things) to a term in
`A`.

`#conv norm_num (3:A) + 10` -- should output `↑13`
`#conv norm_num (3:A) * 10 + 1` -- should output `↑31`

Here are some examples which `norm_num` should solve.  Solve them by hand, writing out what we want
the tactic to do. Since we plan to write a conv-tactic, you should modify the LHS only:

**write everything inside a `conv_lhs =>` block.**

Useful lemmas: -/
#check Nat.cast_zero
#check Nat.cast_one
#check Nat.cast_two -- etc
#check Nat.cast_add
#check Nat.cast_mul

/-! Exercises: -/

example : (0:A) = ↑(nat_lit 0) := by
  sorry

example : (1:A) = nat_lit 1 := by
  -- dropping the `↑` from now on, since Lean will infer it (look at the infoview here)
  sorry

example : (3:A) = nat_lit 3 := by
  sorry

example : (1:A) + 0 = nat_lit 1 := by
  sorry

example : (1:A) + 3 = nat_lit 4 := by
  sorry

example : (1:A) + 2 + 3 = nat_lit 6 := by
  sorry

example : (1:A) * 2 = nat_lit 2 := by
  sorry

example : (3:A) + 7 = nat_lit 10 := by
  sorry

example : (2:A) * 5 = nat_lit 10 := by
  sorry

example : (2:A) * 5 + 1 = nat_lit 11 := by
  sorry

example : (2:A) * 3 * 5 = nat_lit 30 := by
  sorry
