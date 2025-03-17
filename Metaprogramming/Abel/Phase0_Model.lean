import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.NatInt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open Lean Meta Elab Qq Tactic

namespace Mathlib.Tactic.Abel

def eval {n : Nat} (v : Fin n → A) [AddCommGroup A] : (Fin n → ℤ) →+ A where
  toFun c := ∑ i, c i • v i
  map_zero' := by simp
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]

def atom {n : Nat} (k : Fin n) : Fin n → ℤ := fun j ↦ ite (j = k) 1 0

end Mathlib.Tactic.Abel

open Mathlib.Tactic.Abel

set_option trace.debug true

variable {A : Type*} [AddCommGroup A] (a b c x : A)

example : a + c - (b + 0 + c) = (2:ℤ) • a + c - (a + b + c) := by
  let F : (Fin 3 → ℤ) →+ A := eval ![a, b, c]
  have ha : a = F (atom 0) := by simp [atom, eval, F]
  have hb : b = F (atom 1) := by simp [atom, eval, F]
  have hc : c = F (atom 2) := by simp [atom, eval, F]
  have :=
  calc a + c - (b + 0 + c)
      = F (atom 0) + F (atom 2) - (F (atom 1) + 0 + F (atom 2)) := by simp only [ha, hb, hc]
    _ = F (atom 0 + atom 2 - (atom 1 + 0 + atom 2)) := by simp only [map_add, map_sub, map_zero]
    _ = F ![1, -1, 0] := by congr; ext i; fin_cases i <;> rfl
  rw [this]
  sorry

example (P : A → Prop) (hP : P ((1:ℤ) • a + ((0:ℤ) • b + 0))): P (a - b + b) := by
  conv =>
    enter [1]
  sorry
  -- exact hP
