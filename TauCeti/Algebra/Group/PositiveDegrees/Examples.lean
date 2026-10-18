/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.PositiveDegrees.Map
import Mathlib.Data.Int.Interval

/-!
# A degree bound from above gives no cutoff modulus

On `P = {0} ∪ {(a, b) ∈ ℕ² | a ≥ b ≥ 1}` in `ℤ × ℤ` with degree `δ(a, b) = a`, the second
projection `T(a, b) = b` to `(ℤ, ℕ, id)` sends the nonzero elements of `P` to positive integers
and satisfies `δ'(T n) ≤ δ(n)`, yet it underlies no map of positive degree data: every `(j, 1)`
is sent to degree one, so no cutoff modulus can exist. Thus a map of positive degree data needs
a lower bound on the target degree, not an upper one.

## Main definitions

* `TauCeti.PositiveDegrees.wedge`: the positive degree data `P = {0} ∪ {(a, b) | a ≥ b ≥ 1}` on
  `ℤ × ℤ` with degree `δ(a, b) = a`.

## Main results

* `TauCeti.PositiveDegrees.mapsTo_snd_wedge_positive`,
  `TauCeti.PositiveDegrees.int_degree_snd_le_wedge_degree`: the second projection sends `N⁺` into
  the positive integers and does not increase the degree.
* `TauCeti.PositiveDegrees.not_exists_toAddMonoidHom_eq_snd`: no map of positive degree data
  from `wedge` to `int` has the second projection as underlying map.
-/

public section

namespace TauCeti

namespace PositiveDegrees

/-- The positive degree data `P = {0} ∪ {(a, b) ∈ ℕ² | a ≥ b ≥ 1}` on `ℤ × ℤ`, with degree
`δ(a, b) = a`. -/
def wedge : PositiveDegrees (ℤ × ℤ) where
  monoid :=
    { carrier := {p | p = 0 ∨ 1 ≤ p.2 ∧ p.2 ≤ p.1}
      add_mem' := by
        rintro p q (rfl | hp) (rfl | hq)
        · simp
        · simp [hq]
        · simp [hp]
        · exact Or.inr ⟨by simp; omega, by simp; omega⟩
      zero_mem' := Or.inl rfl }
  degree := AddMonoidHom.fst ℤ ℤ
  degree_pos p hp h0 := by
    obtain ⟨a, b⟩ := p
    rcases hp with h | ⟨h₁, h₂⟩
    · exact absurd h h0
    · simp only [AddMonoidHom.coe_fst] at h₁ h₂ ⊢
      omega
  finite_cutoff' k := by
    refine (Set.Finite.prod (Set.finite_Icc 0 (k : ℤ)) (Set.finite_Icc 0 (k : ℤ))).subset ?_
    rintro ⟨a, b⟩ ⟨(h | ⟨h₁, h₂⟩), hk⟩
    · simp_all
    · simp only [AddMonoidHom.coe_fst, Set.mem_prod, Set.mem_Icc] at h₁ h₂ hk ⊢
      omega

@[simp]
theorem mem_wedge_monoid {p : ℤ × ℤ} :
    p ∈ wedge.monoid ↔ p = 0 ∨ 1 ≤ p.2 ∧ p.2 ≤ p.1 := Iff.rfl

@[simp]
theorem wedge_degree : wedge.degree = AddMonoidHom.fst ℤ ℤ := (rfl)

/-- The second projection sends the nonzero elements of `wedge` to positive integers. -/
theorem mapsTo_snd_wedge_positive :
    Set.MapsTo (AddMonoidHom.snd ℤ ℤ) wedge.positive int.positive := by
  rintro ⟨a, b⟩ hp
  rw [mem_positive_iff, mem_wedge_monoid] at hp
  rcases hp with ⟨h | ⟨h₁, -⟩, h0⟩
  · exact absurd h h0
  · simp only [mem_positive_iff, int_monoid, AddSubmonoid.mem_nonneg, AddMonoidHom.coe_snd]
    omega

/-- The second projection does not increase the degree on `wedge`. -/
theorem int_degree_snd_le_wedge_degree {p : ℤ × ℤ} (hp : p ∈ wedge.monoid) :
    int.degree (AddMonoidHom.snd ℤ ℤ p) ≤ wedge.degree p := by
  rcases mem_wedge_monoid.1 hp with rfl | ⟨-, h⟩
  · simp
  · simpa using h

/-- The second projection underlies no map of positive degree data from `wedge` to `int`: the
elements `(j, 1)` of `wedge` all map to degree one. -/
theorem not_exists_toAddMonoidHom_eq_snd :
    ¬ ∃ f : PositiveDegreeMap wedge int, f.toAddMonoidHom = AddMonoidHom.snd ℤ ℤ := by
  rw [PositiveDegreeMap.exists_toAddMonoidHom_eq_iff]
  rintro ⟨-, hfin⟩
  refine Set.infinite_of_injective_forall_mem (f := fun j : ℕ ↦ ((j : ℤ) + 1, (1 : ℤ)))
    (fun i j h ↦ by simpa using h) (fun j ↦ ?_) (hfin 1)
  simp only [Set.mem_inter_iff, SetLike.mem_coe, mem_wedge_monoid, Set.mem_preimage,
    AddMonoidHom.coe_snd, mem_cutoff_iff, int_monoid, AddSubmonoid.mem_nonneg, int_degree,
    AddMonoidHom.id_apply]
  omega

end PositiveDegrees

end TauCeti
