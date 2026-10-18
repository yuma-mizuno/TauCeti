/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Set.MulAntidiagonal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Int.Interval

/-!
# Positive degree data

Positive degree data on an abelian group `N` consist of an additive submonoid `P ⊆ N` and an
additive degree `δ : N → ℤ` that is strictly positive on the nonzero elements of `P` and has
only finitely many elements of `P` in each degree range `δ ≤ k`. These are the gradings of the
Lie algebras whose truncations `g / F^{k+1} g` underlie scattering diagrams: the finiteness of
the cutoffs makes every truncation involve only finitely many degrees. The positivity makes `P`
sharp, and together with the finite cutoffs it leaves every element only finitely many
decompositions as a sum of two elements of `P`.

## Main definitions

* `TauCeti.PositiveDegrees`: an additive submonoid with a degree that is positive on its
  nonzero elements and has finite cutoffs.
* `TauCeti.PositiveDegrees.positive`: the set `N⁺ = P \ {0}` of positive degrees.
* `TauCeti.PositiveDegrees.cutoff`: the finite set of elements of `P` of degree at most `k`.
* `TauCeti.PositiveDegrees.int`: the natural numbers in `ℤ`, with the identity as degree.
* `TauCeti.PositiveDegrees.pi`: the product of finitely many positive degree data, with the sum
  of the degrees. In particular `pi fun _ : ι ↦ int` is `ℕ^ι ⊆ ℤ^ι` with the coordinate sum.

## Main results

* `TauCeti.PositiveDegrees.finite_antidiagonal`: an element of `N` has only finitely many
  decompositions `n = a + b` with `a, b ∈ P`.
* `TauCeti.PositiveDegrees.isPointed_monoid`: `P` is sharp, i.e. `n, -n ∈ P` forces `n = 0`.

## References

* T. Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, Algebraic
  Geometry 4 (2017), §2.1.
* T. Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*, J. Lond.
  Math. Soc. 104 (2021), §2.1.
-/

public section

namespace TauCeti

/-- Positive degree data on an abelian group `N`: an additive submonoid `P` of `N` together with
an additive degree `δ : N → ℤ` that is strictly positive on the nonzero elements of `P`, such that
for every `k : ℕ` only finitely many elements of `P` have degree at most `k`. -/
structure PositiveDegrees (N : Type*) [AddCommGroup N] where
  /-- The submonoid `P` of degrees. -/
  monoid : AddSubmonoid N
  /-- The degree `δ : N → ℤ`. -/
  degree : N →+ ℤ
  degree_pos : ∀ n ∈ monoid, n ≠ 0 → 0 < degree n
  finite_cutoff' : ∀ k : ℕ, {n | n ∈ monoid ∧ degree n ≤ k}.Finite

namespace PositiveDegrees

variable {N : Type*} [AddCommGroup N] (D : PositiveDegrees N)

/-- The positive degrees `N⁺ = P \ {0}`. -/
def positive : Set N := {n | n ∈ D.monoid ∧ n ≠ 0}

/-- The cutoff of order `k`: the elements of `P` of degree at most `k`. -/
def cutoff (k : ℕ) : Set N := {n | n ∈ D.monoid ∧ D.degree n ≤ k}

variable {D}

@[simp]
theorem mem_positive_iff {n : N} : n ∈ D.positive ↔ n ∈ D.monoid ∧ n ≠ 0 := Iff.rfl

@[simp]
theorem mem_cutoff_iff {k : ℕ} {n : N} : n ∈ D.cutoff k ↔ n ∈ D.monoid ∧ D.degree n ≤ k :=
  Iff.rfl

variable (D) in
/-- Each cutoff is finite. -/
theorem finite_cutoff (k : ℕ) : (D.cutoff k).Finite := D.finite_cutoff' k

/-- The degree is nonnegative on `P`. -/
theorem degree_nonneg {n : N} (hn : n ∈ D.monoid) : 0 ≤ D.degree n := by
  rcases eq_or_ne n 0 with rfl | h
  · simp
  · exact (D.degree_pos n hn h).le

/-- An element of `P` has degree zero exactly when it is zero. -/
theorem degree_eq_zero_iff {n : N} (hn : n ∈ D.monoid) : D.degree n = 0 ↔ n = 0 :=
  ⟨fun h ↦ by_contra fun h0 ↦ (D.degree_pos n hn h0).ne' h, fun h ↦ by simp [h]⟩

/-- The positive degrees are the elements of `P` of positive degree. -/
theorem mem_positive_iff_degree_pos {n : N} : n ∈ D.positive ↔ n ∈ D.monoid ∧ 0 < D.degree n :=
  and_congr_right fun hn ↦ ⟨D.degree_pos n hn, fun h h0 ↦ by simp [h0] at h⟩

variable (D) in
theorem zero_mem_cutoff (k : ℕ) : 0 ∈ D.cutoff k := by simp

variable (D) in
/-- The cutoffs grow with their order. -/
theorem monotone_cutoff : Monotone D.cutoff :=
  fun _ _ h _ hn ↦ ⟨hn.1, hn.2.trans (by exact_mod_cast h)⟩

variable (D) in
/-- An element `n` has only finitely many decompositions `n = a + b` with `a, b ∈ P`. -/
theorem finite_antidiagonal (n : N) :
    (Set.antidiagonal (D.monoid : Set N) D.monoid n).Finite := by
  refine (Set.Finite.prod (D.finite_cutoff (D.degree n).toNat)
    (D.finite_cutoff (D.degree n).toNat)).subset ?_
  rintro ⟨a, b⟩ ⟨ha, hb, rfl⟩
  simp only [SetLike.mem_coe] at ha hb
  have := degree_nonneg ha
  have := degree_nonneg hb
  simp only [Set.mem_prod, mem_cutoff_iff, map_add, ha, hb, true_and]
  omega

variable (D) in
/-- The submonoid `P` is sharp: `n, -n ∈ P` forces `n = 0`. -/
theorem isPointed_monoid : D.monoid.IsPointed := fun n hn hneg ↦ by
  have h₁ := degree_nonneg hn
  have h₂ := degree_nonneg hneg
  rw [map_neg] at h₂
  exact (degree_eq_zero_iff hn).1 (by omega)

/-- The natural numbers `ℕ ⊆ ℤ`, with the identity as degree. -/
def int : PositiveDegrees ℤ where
  monoid := AddSubmonoid.nonneg ℤ
  degree := AddMonoidHom.id ℤ
  degree_pos _ hn h0 := lt_of_le_of_ne hn (Ne.symm h0)
  finite_cutoff' k := (Set.finite_Icc 0 (k : ℤ)).subset fun _ hn ↦ hn

@[simp]
theorem int_monoid : int.monoid = AddSubmonoid.nonneg ℤ := (rfl)

@[simp]
theorem int_degree : int.degree = AddMonoidHom.id ℤ := (rfl)

section Pi

variable {ι : Type*} [Fintype ι] {N : ι → Type*} [∀ i, AddCommGroup (N i)]

/-- The product of finitely many positive degree data: `P = ∏ Pᵢ`, and the degree of `n` is
`∑ᵢ δᵢ(nᵢ)`. For `D = fun _ : ι ↦ int` this is `ℕ^ι ⊆ ℤ^ι` with the coordinate sum as degree. -/
def pi (D : ∀ i, PositiveDegrees (N i)) : PositiveDegrees (∀ i, N i) where
  monoid := AddSubmonoid.pi Set.univ fun i ↦ (D i).monoid
  degree := ∑ i, (D i).degree.comp (Pi.evalAddMonoidHom N i)
  degree_pos n hn h0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 h0
    simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
    exact Finset.sum_pos' (fun j _ ↦ degree_nonneg (hn j trivial))
      ⟨i, Finset.mem_univ i, (D i).degree_pos _ (hn i trivial) hi⟩
  finite_cutoff' k := by
    refine (Set.Finite.pi fun i ↦ (D i).finite_cutoff k).subset fun n hn ↦ ?_
    simp only [AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply,
      Pi.evalAddMonoidHom_apply] at hn
    refine fun i _ ↦ ⟨hn.1 i trivial, le_trans ?_ hn.2⟩
    exact Finset.single_le_sum (f := fun j ↦ (D j).degree (n j))
      (fun j _ ↦ degree_nonneg (hn.1 j trivial)) (Finset.mem_univ i)

variable {D : ∀ i, PositiveDegrees (N i)}

@[simp]
theorem mem_pi_monoid {n : ∀ i, N i} : n ∈ (pi D).monoid ↔ ∀ i, n i ∈ (D i).monoid := by
  simp [pi, AddSubmonoid.mem_pi]

@[simp]
theorem pi_degree_apply (n : ∀ i, N i) : (pi D).degree n = ∑ i, (D i).degree (n i) := by
  simp [pi]

end Pi

end PositiveDegrees

end TauCeti
