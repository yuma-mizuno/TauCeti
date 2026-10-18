/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.PartialSups
public import TauCeti.Algebra.Group.PositiveDegrees.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith

/-!
# Maps of positive degree data

A map of positive degree data `(N, P, δ) → (N', P', δ')` is an additive map `T : N → N'` with
`T(N⁺) ⊆ N'⁺` (hence `T(P) ⊆ P'`), together with a monotone cutoff modulus `λ : ℕ → ℕ` such that
`δ(n) > λ(k)` implies `δ'(T n) > k` for `n ∈ P`. The modulus is part of the data: it is what
induces maps from the truncation of order `λ(k)` of a graded object over `N` to the truncation of
order `k` of a graded object over `N'`.

## Main definitions

* `TauCeti.PositiveDegreeMap`: a map of positive degree data with a chosen cutoff modulus.
* `TauCeti.PositiveDegreeMap.id`, `TauCeti.PositiveDegreeMap.comp`: identity (with modulus
  `k ↦ k`) and composition (with the composite modulus in the opposite order).
* `TauCeti.PositiveDegreeMap.ofModulus`: an arbitrary, not necessarily monotone, modulus is
  replaced by its running maximum.
* `TauCeti.PositiveDegreeMap.ofDegreeLeMul`: a bound `δ(n) ≤ c · δ'(T n)` on `P` gives the
  modulus `k ↦ c · k`.
* `TauCeti.PositiveDegreeMap.ofFinitePreimage`: if `T(N⁺) ⊆ N'⁺` and the preimages of the cutoffs
  meet `P` in finite sets, then `k ↦ max {δ(n) | n ∈ P, δ'(T n) ≤ k}` is a modulus, and it is the
  least one.
* `TauCeti.PositiveDegreeMap.ofInjOn`: an additive map injective on `P` with `T(P) ⊆ P'`.
* `TauCeti.PositiveDegreesCat`: the category of positive degree data and their maps.

## Main results

* `TauCeti.PositiveDegreeMap.exists_toAddMonoidHom_eq_iff`: an additive map underlies a map of
  positive degree data exactly when it sends `N⁺` into `N'⁺` and the preimage of each cutoff meets
  `P` in a finite set.
* `TauCeti.PositiveDegreeMap.exists_toAddMonoidHom_eq_addEquiv_and_symm`: an additive isomorphism
  carrying `P` onto `P'` underlies maps of positive degree data in both directions.
* `TauCeti.PositiveDegreeMap.exists_degree_le_mul_of_fg`: if `P` is finitely generated and
  `T(N⁺) ⊆ N'⁺`, then `δ(n) ≤ c · δ'(T n)` on `P` for some `c`, namely the maximum of `δ` on a
  finite set of generators.

## References

* T. Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, Algebraic
  Geometry 4 (2017), §2.1.
* T. Mandel, *Scattering diagrams, theta functions, and refined tropical curve counts*, J. Lond.
  Math. Soc. 104 (2021), §2.1.
-/

public section

namespace TauCeti

open PositiveDegrees

/-- A map of positive degree data `(N, P, δ) → (N', P', δ')`: an additive map `T` sending the
positive degrees `N⁺` into `N'⁺`, with a monotone cutoff modulus `λ` such that `δ(n) > λ(k)`
implies `δ'(T n) > k` for every `n ∈ P`. -/
structure PositiveDegreeMap {N N' : Type*} [AddCommGroup N] [AddCommGroup N']
    (D : PositiveDegrees N) (E : PositiveDegrees N') extends N →+ N' where
  mapsTo_positive' : Set.MapsTo toFun D.positive E.positive
  /-- The cutoff modulus `λ`. -/
  modulus : ℕ →o ℕ
  lt_degree_of_modulus_lt' : ∀ (k : ℕ) ⦃n : N⦄, n ∈ D.monoid → (modulus k : ℤ) < D.degree n →
    (k : ℤ) < E.degree (toFun n)

namespace PositiveDegreeMap

variable {N N' N'' N''' : Type*} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup N'''] {D : PositiveDegrees N} {E : PositiveDegrees N'} {F : PositiveDegrees N''}
  {G : PositiveDegrees N'''}

instance : CoeFun (PositiveDegreeMap D E) fun _ ↦ N → N' := ⟨fun f ↦ f.toAddMonoidHom⟩

@[simp]
theorem toFun_eq_coe (f : PositiveDegreeMap D E) : f.toFun = f.toAddMonoidHom := (rfl)

/-- Two maps of positive degree data agree when their underlying maps and their moduli agree. -/
@[ext]
theorem ext {f g : PositiveDegreeMap D E} (h : ∀ n, f n = g n)
    (hm : ∀ k, f.modulus k = g.modulus k) : f = g := by
  obtain ⟨f, _, μ, _⟩ := f
  obtain ⟨g, _, ν, _⟩ := g
  obtain rfl : f = g := AddMonoidHom.ext h
  obtain rfl : μ = ν := OrderHom.ext _ _ (funext hm)
  rfl

variable (f : PositiveDegreeMap D E)

theorem mapsTo_positive : Set.MapsTo f D.positive E.positive := f.mapsTo_positive'

/-- A map of positive degree data sends `P` into `P'`. -/
theorem mapsTo_monoid : Set.MapsTo f D.monoid E.monoid := by
  intro n hn
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  · exact (mem_positive_iff.1 (f.mapsTo_positive (mem_positive_iff.2 ⟨hn, h0⟩))).1

theorem lt_degree_of_modulus_lt (k : ℕ) {n : N} (hn : n ∈ D.monoid)
    (h : (f.modulus k : ℤ) < D.degree n) : (k : ℤ) < E.degree (f n) :=
  f.lt_degree_of_modulus_lt' k hn h

/-- The contrapositive form of the cutoff condition: elements of `P` whose image has degree at
most `k` have degree at most `λ(k)`. -/
theorem degree_le_modulus {k : ℕ} {n : N} (hn : n ∈ D.monoid) (h : E.degree (f n) ≤ k) :
    D.degree n ≤ f.modulus k :=
  le_of_not_gt fun h' ↦ (f.lt_degree_of_modulus_lt k hn h').not_ge h

/-- The elements of `P` mapping into a cutoff form a finite set: they lie in the cutoff of
order `λ(k)`. -/
theorem finite_inter_preimage_cutoff (k : ℕ) :
    ((D.monoid : Set N) ∩ f ⁻¹' E.cutoff k).Finite :=
  (D.finite_cutoff (f.modulus k)).subset fun _ hn ↦
    mem_cutoff_iff.2 ⟨hn.1, f.degree_le_modulus hn.1 (mem_cutoff_iff.1 hn.2).2⟩

variable (D) in
/-- The identity map of positive degree data, with modulus `k ↦ k`. -/
def id : PositiveDegreeMap D D where
  toAddMonoidHom := AddMonoidHom.id N
  mapsTo_positive' := Set.mapsTo_id _
  modulus := OrderHom.id
  lt_degree_of_modulus_lt' _ _ _ h := h

@[simp]
theorem id_toAddMonoidHom : (id D).toAddMonoidHom = AddMonoidHom.id N := (rfl)

@[simp]
theorem id_modulus : (id D).modulus = OrderHom.id := (rfl)

/-- The composite of `f : D → E` and `g : E → F`. If `f` has modulus `λ` and `g` has modulus
`λ'`, the composite has modulus `λ ∘ λ'`. -/
def comp (g : PositiveDegreeMap E F) (f : PositiveDegreeMap D E) : PositiveDegreeMap D F where
  toAddMonoidHom := g.toAddMonoidHom.comp f.toAddMonoidHom
  mapsTo_positive' := g.mapsTo_positive.comp f.mapsTo_positive
  modulus := f.modulus.comp g.modulus
  lt_degree_of_modulus_lt' k _ hn h :=
    g.lt_degree_of_modulus_lt k (f.mapsTo_monoid hn) (f.lt_degree_of_modulus_lt _ hn h)

@[simp]
theorem comp_toAddMonoidHom (g : PositiveDegreeMap E F) :
    (g.comp f).toAddMonoidHom = g.toAddMonoidHom.comp f.toAddMonoidHom := (rfl)

@[simp]
theorem comp_modulus (g : PositiveDegreeMap E F) :
    (g.comp f).modulus = f.modulus.comp g.modulus := (rfl)

@[simp]
theorem id_comp : (id E).comp f = f := by ext <;> simp

@[simp]
theorem comp_id : f.comp (id D) = f := by ext <;> simp

theorem comp_assoc (g : PositiveDegreeMap E F) (h : PositiveDegreeMap F G) :
    (h.comp g).comp f = h.comp (g.comp f) := by ext <;> simp

/-! ### Constructions of maps of positive degree data -/

/-- A map of positive degree data from an arbitrary, not necessarily monotone, cutoff modulus
`μ`. The modulus is replaced by its running maximum `k ↦ max {μ 0, …, μ k}`. -/
def ofModulus (T : N →+ N') (hT : Set.MapsTo T D.positive E.positive) (μ : ℕ → ℕ)
    (hμ : ∀ (k : ℕ) ⦃n : N⦄, n ∈ D.monoid → (μ k : ℤ) < D.degree n → (k : ℤ) < E.degree (T n)) :
    PositiveDegreeMap D E where
  toAddMonoidHom := T
  mapsTo_positive' := hT
  modulus := partialSups μ
  lt_degree_of_modulus_lt' k _ hn h :=
    hμ k hn (lt_of_le_of_lt (by exact_mod_cast le_partialSups μ k) h)

@[simp]
theorem ofModulus_toAddMonoidHom (T : N →+ N') (hT : Set.MapsTo T D.positive E.positive)
    (μ : ℕ → ℕ) (hμ) : (ofModulus T hT μ hμ).toAddMonoidHom = T := (rfl)

@[simp]
theorem ofModulus_modulus (T : N →+ N') (hT : Set.MapsTo T D.positive E.positive)
    (μ : ℕ → ℕ) (hμ) : (ofModulus T hT μ hμ).modulus = partialSups μ := (rfl)

/-- A map of positive degree data from a bound `δ(n) ≤ c · δ'(T n)` on `P`, with modulus
`k ↦ c · k`. -/
def ofDegreeLeMul (T : N →+ N') (hT : Set.MapsTo T D.positive E.positive) (c : ℕ)
    (hc : ∀ n ∈ D.monoid, D.degree n ≤ c * E.degree (T n)) : PositiveDegreeMap D E where
  toAddMonoidHom := T
  mapsTo_positive' := hT
  modulus := ⟨(c * ·), fun _ _ h ↦ Nat.mul_le_mul_left c h⟩
  lt_degree_of_modulus_lt' k n hn h := by
    -- `h` is stated for the bundled modulus; restate it for `c * k`.
    have h₁ : ((c * k : ℕ) : ℤ) < D.degree n := h
    have h₂ := hc n hn
    push_cast at h₁
    have h₃ : (k : ℤ) < E.degree (T n) := by nlinarith [Int.natCast_nonneg c]
    exact h₃

@[simp]
theorem ofDegreeLeMul_toAddMonoidHom (T : N →+ N') (hT : Set.MapsTo T D.positive E.positive)
    (c : ℕ) (hc) : (ofDegreeLeMul T hT c hc).toAddMonoidHom = T := (rfl)

@[simp]
theorem ofDegreeLeMul_modulus_apply (T : N →+ N') (hT : Set.MapsTo T D.positive E.positive)
    (c : ℕ) (hc) (k : ℕ) : (ofDegreeLeMul T hT c hc).modulus k = c * k := (rfl)

/-- If `T(N⁺) ⊆ N'⁺` and `δ ≤ c` on a set of generators of `P`, then `δ(n) ≤ c · δ'(T n)` for
every `n ∈ P`. -/
theorem degree_le_mul_of_closure_eq {T : N →+ N'} (hT : Set.MapsTo T D.positive E.positive)
    {S : Set N} (hS : AddSubmonoid.closure S = D.monoid) {c : ℕ}
    (hc : ∀ s ∈ S, D.degree s ≤ c) {n : N} (hn : n ∈ D.monoid) :
    D.degree n ≤ c * E.degree (T n) := by
  rw [← hS] at hn
  induction hn using AddSubmonoid.closure_induction with
  | mem s hs =>
    have hsP : s ∈ D.monoid := hS ▸ AddSubmonoid.subset_closure hs
    rcases eq_or_ne s 0 with rfl | h0
    · simp
    · have h₁ := (mem_positive_iff_degree_pos.1 (hT (mem_positive_iff.2 ⟨hsP, h0⟩))).2
      have h₂ := hc s hs
      nlinarith
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, mul_add]; omega

/-- If `P` is finitely generated and `T(N⁺) ⊆ N'⁺`, then `δ(n) ≤ c · δ'(T n)` on `P` for some
`c : ℕ`. -/
theorem exists_degree_le_mul_of_fg (hP : D.monoid.FG) {T : N →+ N'}
    (hT : Set.MapsTo T D.positive E.positive) :
    ∃ c : ℕ, ∀ n ∈ D.monoid, D.degree n ≤ c * E.degree (T n) := by
  obtain ⟨S, hS, hSfin⟩ := (AddSubmonoid.fg_iff _).1 hP
  obtain ⟨c, hc⟩ := (hSfin.image D.degree).bddAbove
  exact ⟨c.toNat, fun n hn ↦ degree_le_mul_of_closure_eq hT hS
    (fun s hs ↦ (hc ⟨s, hs, rfl⟩).trans (Int.self_le_toNat c)) hn⟩

/-- The modulus `k ↦ max {δ(n) | n ∈ P, δ'(T n) ≤ k}` of an additive map for which these sets are
finite. -/
noncomputable def finitePreimageModulus (T : N →+ N')
    (hfin : ∀ k : ℕ, ((D.monoid : Set N) ∩ T ⁻¹' E.cutoff k).Finite) : ℕ →o ℕ where
  toFun k := sSup ((fun n ↦ (D.degree n).toNat) '' ((D.monoid : Set N) ∩ T ⁻¹' E.cutoff k))
  monotone' a b hab := by
    refine csSup_le_csSup ((hfin b).image _).bddAbove ⟨0, 0, ?_, by simp⟩ ?_
    · simp
    · exact Set.image_mono (Set.inter_subset_inter_right _ (Set.preimage_mono
        (E.monotone_cutoff hab)))

theorem finitePreimageModulus_apply (T : N →+ N')
    (hfin : ∀ k : ℕ, ((D.monoid : Set N) ∩ T ⁻¹' E.cutoff k).Finite) (k : ℕ) :
    finitePreimageModulus T hfin k =
      sSup ((fun n ↦ (D.degree n).toNat) '' ((D.monoid : Set N) ∩ T ⁻¹' E.cutoff k)) := (rfl)

/-- The degree of an element of `P` whose image lies in the cutoff of order `k` is at most
`finitePreimageModulus T hfin k`. -/
theorem degree_le_finitePreimageModulus {T : N →+ N'}
    (hfin : ∀ k : ℕ, ((D.monoid : Set N) ∩ T ⁻¹' E.cutoff k).Finite) {k : ℕ} {n : N}
    (hn : n ∈ D.monoid) (hTn : T n ∈ E.cutoff k) :
    D.degree n ≤ finitePreimageModulus T hfin k := by
  rw [finitePreimageModulus_apply]
  have : (D.degree n).toNat ≤ _ :=
    le_csSup ((hfin k).image fun n ↦ (D.degree n).toNat).bddAbove ⟨n, ⟨hn, hTn⟩, rfl⟩
  have := degree_nonneg hn
  omega

/-- A map of positive degree data from an additive map with `T(N⁺) ⊆ N'⁺` whose preimages of the
cutoffs meet `P` in finite sets, with the modulus `k ↦ max {δ(n) | n ∈ P, δ'(T n) ≤ k}`. -/
noncomputable def ofFinitePreimage (T : N →+ N') (hT : Set.MapsTo T D.positive E.positive)
    (hfin : ∀ k : ℕ, ((D.monoid : Set N) ∩ T ⁻¹' E.cutoff k).Finite) : PositiveDegreeMap D E where
  toAddMonoidHom := T
  mapsTo_positive' := hT
  modulus := finitePreimageModulus T hfin
  lt_degree_of_modulus_lt' k n hn h := by
    by_contra h'
    have hTn : T n ∈ E.cutoff k := by
      refine mem_cutoff_iff.2 ⟨?_, by simpa using h'⟩
      rcases eq_or_ne n 0 with rfl | h0
      · simp
      · exact (mem_positive_iff.1 (hT (mem_positive_iff.2 ⟨hn, h0⟩))).1
    exact (degree_le_finitePreimageModulus hfin hn hTn).not_gt h

@[simp]
theorem ofFinitePreimage_toAddMonoidHom (T : N →+ N') (hT : Set.MapsTo T D.positive E.positive)
    (hfin) : (ofFinitePreimage T hT hfin).toAddMonoidHom = T := (rfl)

@[simp]
theorem ofFinitePreimage_modulus (T : N →+ N') (hT : Set.MapsTo T D.positive E.positive)
    (hfin) : (ofFinitePreimage T hT hfin).modulus = finitePreimageModulus T hfin := (rfl)

/-- The modulus of `ofFinitePreimage` is the least modulus of any map of positive degree data
with the same underlying map. -/
theorem finitePreimageModulus_le
    (hfin : ∀ k : ℕ, ((D.monoid : Set N) ∩ f.toAddMonoidHom ⁻¹' E.cutoff k).Finite) :
    finitePreimageModulus f.toAddMonoidHom hfin ≤ f.modulus := by
  intro k
  rw [finitePreimageModulus_apply]
  refine csSup_le ⟨0, 0, by simp⟩ ?_
  rintro _ ⟨n, ⟨hn, hTn⟩, rfl⟩
  have := f.degree_le_modulus hn (mem_cutoff_iff.1 hTn).2
  dsimp only
  omega

/-- An additive map underlies a map of positive degree data exactly when it sends `N⁺` into `N'⁺`
and the preimage of each cutoff meets `P` in a finite set. -/
theorem exists_toAddMonoidHom_eq_iff {T : N →+ N'} :
    (∃ f : PositiveDegreeMap D E, f.toAddMonoidHom = T) ↔
      Set.MapsTo T D.positive E.positive ∧
        ∀ k : ℕ, ((D.monoid : Set N) ∩ T ⁻¹' E.cutoff k).Finite := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.mapsTo_positive, f.finite_inter_preimage_cutoff⟩
  · rintro ⟨hT, hfin⟩
    exact ⟨ofFinitePreimage T hT hfin, rfl⟩

/-- An additive map injective on `P` with `T(P) ⊆ P'` sends `N⁺` into `N'⁺`. -/
theorem mapsTo_positive_of_injOn {T : N →+ N'} (hinj : Set.InjOn T D.monoid)
    (hT : Set.MapsTo T D.monoid E.monoid) : Set.MapsTo T D.positive E.positive := by
  intro n hn
  rw [mem_positive_iff] at hn ⊢
  refine ⟨hT hn.1, fun h ↦ hn.2 (hinj hn.1 D.monoid.zero_mem ?_)⟩
  simpa using h

/-- For an additive map injective on `P` with `T(P) ⊆ P'`, the elements of `P` mapping into a
cutoff form a finite set. -/
theorem finite_inter_preimage_cutoff_of_injOn {T : N →+ N'} (hinj : Set.InjOn T D.monoid)
    (k : ℕ) : ((D.monoid : Set N) ∩ T ⁻¹' E.cutoff k).Finite :=
  Set.Finite.of_finite_image ((E.finite_cutoff k).subset (Set.image_subset_iff.2
    Set.inter_subset_right)) (hinj.mono Set.inter_subset_left)

/-- A map of positive degree data from an additive map injective on `P` with `T(P) ⊆ P'`, with the
modulus `k ↦ max {δ(n) | n ∈ P, δ'(T n) ≤ k}`. -/
noncomputable def ofInjOn (T : N →+ N') (hinj : Set.InjOn T D.monoid)
    (hT : Set.MapsTo T D.monoid E.monoid) : PositiveDegreeMap D E :=
  ofFinitePreimage T (mapsTo_positive_of_injOn hinj hT)
    (finite_inter_preimage_cutoff_of_injOn hinj)

@[simp]
theorem ofInjOn_toAddMonoidHom (T : N →+ N') (hinj : Set.InjOn T D.monoid)
    (hT : Set.MapsTo T D.monoid E.monoid) : (ofInjOn T hinj hT).toAddMonoidHom = T := (rfl)

@[simp]
theorem ofInjOn_modulus (T : N →+ N') (hinj : Set.InjOn T D.monoid)
    (hT : Set.MapsTo T D.monoid E.monoid) :
    (ofInjOn T hinj hT).modulus =
      finitePreimageModulus T (finite_inter_preimage_cutoff_of_injOn (E := E) hinj) := (rfl)

/-- An additive isomorphism carrying `P` onto `P'` underlies maps of positive degree data in both
directions; `ofInjOn` provides them, with the moduli `k ↦ max {δ(n) | n ∈ P, δ'(e n) ≤ k}` and
`k ↦ max {δ'(n') | n' ∈ P', δ(e⁻¹ n') ≤ k}`. -/
theorem exists_toAddMonoidHom_eq_addEquiv_and_symm (e : N ≃+ N')
    (he : D.monoid.map e = E.monoid) :
    (∃ f : PositiveDegreeMap D E, f.toAddMonoidHom = e) ∧
      ∃ g : PositiveDegreeMap E D, g.toAddMonoidHom = e.symm := by
  refine ⟨⟨ofInjOn e e.injective.injOn fun _ hn ↦ he ▸ AddSubmonoid.mem_map_of_mem e hn, rfl⟩,
    ⟨ofInjOn e.symm e.symm.injective.injOn fun n hn ↦ ?_, rfl⟩⟩
  rw [← he] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  simpa using hm

end PositiveDegreeMap

/-! ### The category of positive degree data -/

universe u

/-- Positive degree data on abelian groups in a fixed universe, as the objects of a category whose
morphisms are the maps of positive degree data. -/
structure PositiveDegreesCat : Type (u + 1) where
  /-- The underlying abelian group. -/
  carrier : Type u
  /-- The abelian group structure on the carrier. -/
  [addCommGroup : AddCommGroup carrier]
  /-- The positive degree data on the underlying group. -/
  degrees : PositiveDegrees carrier

attribute [instance] PositiveDegreesCat.addCommGroup

namespace PositiveDegreesCat

open CategoryTheory

instance : Category PositiveDegreesCat.{u} where
  Hom X Y := PositiveDegreeMap X.degrees Y.degrees
  id X := PositiveDegreeMap.id X.degrees
  comp f g := g.comp f
  id_comp := PositiveDegreeMap.comp_id
  comp_id := PositiveDegreeMap.id_comp
  assoc f g h := (PositiveDegreeMap.comp_assoc f g h).symm

@[simp]
theorem id_def (X : PositiveDegreesCat.{u}) : 𝟙 X = PositiveDegreeMap.id X.degrees := (rfl)

@[simp]
theorem comp_def {X Y Z : PositiveDegreesCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = PositiveDegreeMap.comp g f := (rfl)

end PositiveDegreesCat

end TauCeti
