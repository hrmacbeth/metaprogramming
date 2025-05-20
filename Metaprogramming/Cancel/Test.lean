import Mathlib
import Metaprogramming.Cancel.Attribute

open Real Set

/-! ### Lemmas to tag @[cancel] -/

#check lt_of_add_lt_add_right
#check lt_of_mul_lt_mul_left
#check add_left_cancel

theorem lt_of_inv_lt_inv₀ {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [ZeroLEOneClass G₀]
    [PosMulReflectLT G₀] {a b : G₀} [MulPosStrictMono G₀] [PosMulStrictMono G₀] (ha : 0 < a) :
    a⁻¹ < b⁻¹ → b < a := by
  intro h
  rwa [inv_lt_inv₀ ha] at h
  rw [← inv_pos] at ha ⊢
  exact ha.trans h

lemma smul_left_injective₀
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    {a b : R} {x : M} (hx : x ≠ 0) (h : a • x = b • x) : a = b := by
   rwa [← sub_eq_zero, ← sub_smul, smul_eq_zero_iff_left hx, sub_eq_zero] at h

alias ⟨Topology.IsInducing.of_specializes, _⟩ := Topology.IsInducing.specializes_iff

theorem le_of_cos_le_cos {a b : ℝ} (ha : a ∈ Icc 0 π) (hb : b ∈ Icc 0 π) (h : cos a ≤ cos b) :
    b ≤ a := by
  rwa [← Real.strictAntiOn_cos.le_iff_le ha hb]


-- add in an "unfolded" version so that our @[cancel] check works
#check exp_injective
#check Real.injOn_cos


/-! ### Tests -/

example {a b x y : ℝ} (h : 0 ≤ a) (h : a * x + b < a * y + b) : True := by
  apply lt_of_add_lt_add_right at h
  replace h := lt_of_mul_lt_mul_left h (by positivity)
  trivial

example {a b x y : ℝ} (h : exp (3 + x) = exp (3 + y)) : True := by
  apply exp_injective at h
  apply add_left_cancel at h
  trivial

example {x y : ℝ} (h : cos x = cos y) : True := by
  apply Real.injOn_cos at h
  trivial
  all_goals sorry

example {x y : ℝ} (hx : 0 < x) (h : x⁻¹ < y⁻¹) : True := by
  apply lt_of_inv_lt_inv₀ (by positivity) at h
  trivial

example {R : Type*} [Monoid R] {a b x : R} (ha : IsUnit x) (h : a * x = b * x) : True := by
  apply IsUnit.mul_left_injective ‹_› at h
  trivial

example {R : Type*} [Ring R] [NoZeroDivisors R]
    {a b x : R} (hx : x ≠ 0) (h : a * x = b * x) : True := by
  apply mul_right_cancel₀ ‹_›  at h
  trivial

example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]
    {a b : R} {x : M} (hx : x ≠ 0) (h : a • x = b • x) : True := by
  apply smul_left_injective₀ ‹_› at h
  trivial

open CategoryTheory in
example {C : Type*} [Category C] {X Y Z : C} (f f' : X ⟶ Y) (g : Y ⟶ Z)
  (h : f ≫ g = f' ≫ g) [Mono g] : True := by
  apply Mono.right_cancellation at h
  trivial

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    {x y : X} (h : Topology.IsInducing f) (h : f x ⤳ f y) : x ⤳ y := by
  apply Topology.IsInducing.of_specializes ‹_› at h
  exact h

example {a x y : ℝ} (h : Real.cos (x + a) ≤ Real.cos (y + a)) : True := by
  apply le_of_cos_le_cos at h
  apply le_of_add_le_add_right at h
  trivial
  all_goals sorry
