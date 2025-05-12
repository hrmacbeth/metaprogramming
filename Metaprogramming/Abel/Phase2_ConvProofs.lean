import Lean.Elab.Tactic.Conv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Util.Qq

open Lean Meta Elab Qq Tactic

namespace Mathlib.Tactic.Abel

/-! ## Code from before -/

def eval {n : Nat} (v : Fin n → A) [AddCommGroup A] : (Fin n → ℤ) →+ A where
  toFun c := ∑ i, c i • v i
  map_zero' := by simp
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]

def atom {n : Nat} (k : Fin n) : Fin n → ℤ := fun j ↦ ite (j = k) 1 0

variable {u : Level} {A : Q(Type u)} (iA : Q(AddCommGroup $A)) {n : Nat} (atoms : Fin n → Q($A))

def glue : ∀ {n : Nat}, (Fin n → Q($A)) → Q(Fin $n → $A)
  | 0, _ =>  q(![])
  | n + 1, v =>
    let V : Q(Fin $n → $A) := glue (Matrix.vecTail v)
    q(Matrix.vecCons $(Matrix.vecHead v) $V)

def qEval (v : Fin n → Q($A)) (c : Fin n → ℤ) : Q($A) :=
  let mkInt (a : ℤ) : Q(ℤ) := q($a)
  q(eval $(glue v) $(glue (u := 0) (mkInt ∘ c)))

/-! ### Tests: how the gluing works -/
section

def _root_.e : Nat := sorry
attribute [-app_unexpander] Matrix.vecEmptyUnexpander Matrix.vecConsUnexpander
#eval glue ![q(e), q(e)]

end

/-! ### Main algorithm -/

def findAtom (x : Q($A)) : MetaM (Σ c : Fin n → ℤ, Q($x = $(qEval iA atoms c))) := do
  let some k ← (Array.ofFn atoms).findIdxM? (isDefEq x) |
    throwError "provided list of atoms is not complete"
  if h : k < n then
    let k : Fin n := ⟨k, h⟩
    pure ⟨atom k, q(sorry)⟩
  else
    unreachable!

/-- The main algorithm behind the `abel` tactic: partially-normalizing an expression in an additive
abelian group `A` into the form ![c1, c2, ... c_k],
where c1, c2, ... are integers, each the coefficient of the corresponding atom x1, x2, ... in the
provided expression. -/
partial def normalForm (x : Q($A)) : MetaM (Σ c : Fin n → ℤ, Q($x = $(qEval iA atoms c))) := do
  match x with
  /- parse an addition: `x₁ + x₂` -/
  | ~q($x₁ + $x₂) =>
    let ⟨c₁, pf₁⟩ ← normalForm x₁
    let ⟨c₂, pf₂⟩ ← normalForm x₂
    pure ⟨c₁ + c₂, q(sorry)⟩
  /- parse a subtraction: `x₁ - x₂` -/
  | ~q($x₁ - $x₂) =>
    let ⟨c₁, pf₁⟩ ← normalForm x₁
    let ⟨c₂, pf₂⟩ ← normalForm x₂
    pure ⟨c₁ - c₂, q(sorry)⟩
  /- parse a negation: `-x` -/
  | ~q(- $x) =>
    let ⟨c, pf⟩ ← normalForm x
    pure ⟨- c, q(sorry)⟩
  /- parse a scalar multiplication: `(n : ℤ) • x` -/
  | ~q(($n : ℤ) • $x) =>
    let ⟨c, pf⟩ ← normalForm x
    let some n := Expr.int? n | findAtom iA atoms x -- if `n` is not a numeral, just treat as atom
    pure ⟨n • c, q(sorry)⟩
  /- parse a `(0:A)` -/
  | ~q(0) =>
    pure ⟨0, q(sorry)⟩
  /- anything else needs to be on the list of atoms -/
  | _ => findAtom iA atoms x

/-!

You can leave the rest of the file unchanged.

### Boilerplate -/

/-- Conv tactic for abelian-group-normalization, relative to a provided list of atoms.  Wraps the
`MetaM` normalization function `Tactic.Abel.normalForm`. -/
elab "abel_with_atoms" exprs:(ppSpace colGt term:max)* : conv => do
  -- find the expression `x` to `conv` on
  let x ← Conv.getLhs
  -- infer `u` and `A : Q(Type u)` such that `x : Q($A)`
  let ⟨u, A, _⟩ ← inferTypeQ' x
  -- find an `AddCommGroup` instance on `A`
  let iA : Q(AddCommGroup $A) ← synthInstanceQ q(AddCommGroup $A)
  -- parse the provided "atom" terms as a vector of expressions in `Q($A)`
  let exprs ← exprs.mapM (Elab.Tactic.elabTerm · none)
  let exprsFn : Fin exprs.size → Q($A) := getElem! exprs
  -- run the core normalization function `normalForm` on `x`, relative to the atoms
  let ⟨x', pf⟩ ← normalForm iA exprsFn x
  -- convert `x` to the output of the normalization
  Conv.applySimpResult { expr := qEval iA exprsFn x', proof? := some pf }

/-! ### Tests -/

set_option trace.debug true

variable {A : Type*} [AddCommGroup A] (a b c x : A)

#conv abel_with_atoms a b => a + b - (a + b)
#conv abel_with_atoms a b c => a + c - (b + 0 + c)
#conv abel_with_atoms a b c => -(b + 0 + c)
#conv abel_with_atoms a b c => a + b + (-2) • c + a

example (P : A → Prop) : P (a - b + b) := by
  conv =>
    enter [1]
    abel_with_atoms a b
  show P ((eval ![a, b]) ![1, 0])
  sorry

example (P : A → Prop) : P (a + c - (b + 0 + c)) := by
  conv =>
    enter [1]
    abel_with_atoms a b c
  show P ((eval ![a, b,c ]) ![1, -1, 0])
  sorry

example (P : A → Prop) : P (-(b + 0 + c)) := by
  conv =>
    enter [1]
    abel_with_atoms a b c
  show P ((eval ![a, b,c ]) ![0, -1, -1])
  sorry

example (P : A → Prop) : P (a + b + (-2) • c + a) := by
  conv =>
    enter [1]
    abel_with_atoms a b c
  show P ((eval ![a, b,c ]) ![2, 1, -2])
  sorry
