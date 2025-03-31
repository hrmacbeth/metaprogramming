import Lean.Elab.Tactic.Conv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Util.Qq

open Lean Meta Elab Qq Tactic

namespace Mathlib.Tactic.Abel

/-! ## Code from before -/

def eval {n : Nat} (v : Fin n → A) [AddCommGroup A] : (Fin n → ℤ) →+ A where
  toFun c := ∑ i, c i • v i
  map_zero' := by simp
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]

def atom {n : Nat} (k : Fin n) : Fin n → ℤ := fun j ↦ ite (j = k) 1 0

/-! ## New code -/

def _root_.e : Nat := sorry

section
attribute [-app_unexpander] Matrix.vecEmptyUnexpander Matrix.vecConsUnexpander

variable {u : Level} {A : Q(Type u)} (iA : Q(AddCommGroup $A)) {n : Nat} (atoms : Fin n → Q($A))

def glue : ∀ {n : Nat}, (Fin n → Q($A)) → Q(Fin $n → $A)
  | 0, _ =>  q(Matrix.vecEmpty)
  | n + 1, v =>
    let V : Q(Fin $n → $A) := glue (Matrix.vecTail v)
    q(Matrix.vecCons $(Matrix.vecHead v) $V)

#eval glue ![q(e), q(e)]

def qEval (v : Fin n → Q($A)) (c : Fin n → ℤ) : Q($A) :=
  let mkInt (a : ℤ) : Q(ℤ) := q($a)
  q(eval $(glue v) $(glue (u := 0) (mkInt ∘ c)))
end

def mkAtom {n : ℕ} (i : Fin n) : ℤ := ite ((i:ℕ) == 0) 1 0

#eval mkAtom (n := 3)

elab "make_eval " exprs:(ppSpace colGt term:max)* : term => do
  -- parse the provided "atom" terms as a vector of expressions
  let exprs ← exprs.mapM (Term.elabTerm · none)
  let exprsFn (i : Fin _ ) : Expr := exprs[i]
  -- infer `u` and `A : Q(Type u)` such that `x : Q($A)`
  let ⟨u, A, _⟩ ← inferTypeQ' exprs[0]!
  -- find an `AddCommGroup` instance on `A`
  let iA : Q(AddCommGroup $A) ← synthInstanceQ q(AddCommGroup $A)
  return qEval iA exprsFn mkAtom

variable {A : Type} [AddCommGroup A] (a b c : A) in
#check make_eval a b c

/-!

You can leave the rest of the file unchanged.

### Tests -/

set_option trace.debug true

variable {A : Type*} [AddCommGroup A] (a b c x : A)

#conv abel_with_atoms a b => a
#conv abel_with_atoms a b c => b
#conv abel_with_atoms a b c => c
#conv abel_with_atoms a (a + b) c => a + b

set_option trace.Elab.congr true
example (P : A → Prop) (hP : P ((1:ℤ) • a + ((0:ℤ) • b + 0))) : P a := by
  sorry


variable {A : Type*} [AddCommGroup A] (a b c x : A)

example : a + c - (b + 0 + c) = (2:ℤ) • a + c - (a + b + c) := by
  sorry
