import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Util.Qq
import Mathlib.Algebra.Ring.Int.Defs

open Lean Meta Elab Qq Tactic

/-!
## Phase 2: Normalization algorithm with proofs

-/

section
variable {u : Level} {A : Q(Type u)} (iA : Q(Semiring $A))


/-- The main algorithm behind the `norm_num` tactic: normalizing an arithmetic expression in a
semiring `A` to a numeral. -/
partial def normalForm (x : Q($A)) : MetaM (Σ n : ℕ, Q($x = $n)) := do
  match x with
  | ~q($a + $b) =>
    let ⟨m, pf₁⟩ ← normalForm a
    let ⟨n, pf₂⟩ ← normalForm b
    return ⟨m + n, q(sorry)⟩
  | ~q($a * $b) =>
    let ⟨m, pf₁⟩ ← normalForm a
    let ⟨n, pf₂⟩ ← normalForm b
    return ⟨m * n, q(sorry)⟩
  | _ =>
    let some n := Expr.nat? x | throwError "atom {x} is not a numeral"
    return ⟨n, q(sorry)⟩


/- ### Boilerplate and tests -/


elab "norm_num" : conv => do
  -- get the expression to be conv'd
  let x ← Conv.getLhs
  -- find the type `A` of that expression
  let ⟨u, A, x⟩ ← inferTypeQ' x
  -- look for a semiring structure on `A`
  let iA : Q(Semiring $A) ← synthInstanceQ q(Semiring $A)
  -- run normalization algorithm
  let ⟨n, pf⟩ ← normalForm iA x
  -- change to the expression `q(↑$n)`, justifying using the proof `pf`
  Conv.applySimpResult { expr := q(($n : $A)), proof? := some pf }

elab "norm_num" : tactic => liftMetaFinishingTactic fun g ↦ do
  let tgt ← g.getType
  let some (α, a, b) := tgt.eq? | throwError "norm_num tactic proves only equality goals"
  -- find the type `A` of that expression
  let ⟨u, A, a⟩ ← inferTypeQ' a
  -- look for a semiring structure on `A`
  let iA : Q(Semiring $A) ← synthInstanceQ q(Semiring $A)
  let ⟨na, pf_a⟩ ← normalForm iA a
  let ⟨nb, pf_b⟩ ← normalForm iA b
  throwError "LHS normalizes to {na}, RHS normalizes to {nb}"

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
