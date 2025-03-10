import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Util.Qq
import Mathlib.Algebra.Ring.Int.Defs

open Lean Meta Elab Qq Tactic

/-!
## Phase 1: Normalization algorithm without proofs

-/

section
variable {u : Level} {A : Q(Type u)} (iA : Q(Semiring $A))

/-- The main algorithm behind the `norm_num` tactic: normalizing an arithmetic expression in a
semiring `A` to a numeral. -/
partial def normalForm (x : Q($A)) : MetaM (Σ n : ℕ, Q($x = $n)) := do
  return ⟨37, q(sorry)⟩


/- ### Boilerplate and tests -/


elab "norm_num" : conv => do
  let x ← Conv.getLhs
  let ⟨u, A, x⟩ ← inferTypeQ' x
  let iA : Q(Semiring $A) ← synthInstanceQ q(Semiring $A)
  let ⟨n, pf⟩ ← normalForm iA x
  Conv.applySimpResult { expr := q(($n : $A)), proof? := some pf }

end

set_option trace.debug true

variable {A : Type*} [Semiring A] (x : A)

#conv norm_num => (0:A)
#conv norm_num => (1:A)
#conv norm_num => (3:A)

#conv norm_num => (3:A) + 7
#conv norm_num => (3:A) * 7
#conv norm_num => (3:A) + 7 * 1
#conv norm_num => (1:A) + 0 + 1 + 0
