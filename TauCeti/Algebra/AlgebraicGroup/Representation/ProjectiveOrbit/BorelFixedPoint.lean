/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.FixedPoint
public import TauCeti.Algebra.AlgebraicGroup.Representation.Stabilizer
import TauCeti.Algebra.AlgebraicGroup.Connected.Irreducible
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Boundary
import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.ClosedOrbit

/-!
# The Borel fixed point theorem for projective orbits

Let `G = Spec H` be a reduced connected solvable affine group of finite type over an
algebraically closed field `k`, acting on the projective space `P(V)` of a finite-dimensional
representation. Every closed subset `Z` of `P(V)` that is stable under the rational translations
and contains a line contains a fixed point of `G`: a line `[m']` whose orbit is `{[m']}`, so that
the line `k ∙ m'` is stable under every rational point of `G` and its stabilizer is all of `G`.
In particular the closure of every orbit contains such a line.

The proof assembles three results. A connected group over an algebraically closed field is
irreducible (`CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace`), so by the
closed-orbit lemma the closure of every orbit contains a closed orbit
(`exists_isClosed_range_projectiveOrbitMap_subset_closure`). A closed orbit of a reduced
connected solvable group is a point
(`range_projectiveOrbitMap_eq_singleton_of_isClosed_of_isSolvable`): it is affine by
Lie–Kolchin and proper, hence finite, and it is connected. Finally a closed
translation-invariant set containing a line contains its whole orbit
(`range_projectiveOrbitMap_subset_iff_of_isClosed`).

Reducedness of the group is needed for the second step, and for the passage from stability
under the rational points to the vanishing of the stabilizer Hopf ideal
(`Submodule.stabilizerHopfIdeal_eq_bot_of_forall_basePointsRepresentation_mem`).

## Main declarations

* `TauCeti.Comodule.exists_projectivePointTranslation_eq_mem_of_isClosed_of_isSolvable`:
  the **Borel fixed point theorem**: a closed translation-invariant subset of `P(V)` containing
  a line contains a point fixed by every rational translation.
* `TauCeti.Comodule.exists_map_span_eq_span_mem_of_isClosed_of_isSolvable`,
  `TauCeti.Comodule.exists_stabilizerHopfIdeal_span_eq_bot_mem_of_isClosed_of_isSolvable`:
  such a subset contains a line stable under every rational point, whose stabilizer is the
  whole group.
* `TauCeti.Comodule.exists_range_projectiveOrbitMap_eq_singleton_subset_closure_of_isSolvable`:
  the closure of every orbit contains an orbit consisting of one point.
* `TauCeti.Comodule.exists_map_span_eq_span_mem_closure_of_isSolvable`,
  `TauCeti.Comodule.exists_stabilizerHopfIdeal_span_eq_bot_mem_closure_of_isSolvable`: the
  closure of every orbit contains a stable line, whose stabilizer is the whole group.

## References

* C. Chevalley, *Classification des groupes de Lie algébriques*, Séminaire Chevalley
  1956–1958, Exposé 5, Théorème 3.
* A. Borel, *Linear Algebraic Groups*, 2nd ed., GTM 126, §10.4.
* J. S. Milne, *Algebraic Groups* (2017), Theorem 17.5.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
  [Group.IsSolvable (WithConv (H →ₐ[k] k))]
  [AddCommGroup M] [Module k M] [Comodule k H M] [Module.Finite k M]

/-- The closure of every projective orbit of a reduced connected solvable affine group contains
an orbit consisting of a single point. -/
theorem exists_range_projectiveOrbitMap_eq_singleton_subset_closure_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m) :
    ∃ (m' : M) (hm' : Module.IsUnimodular k m'),
      Set.range (projectiveOrbitMap (H := H) m' hm') =
          {projectiveOrbitMap (H := H) m' hm'
            (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))} ∧
        Set.range (projectiveOrbitMap (H := H) m' hm') ⊆
          closure (Set.range (projectiveOrbitMap (H := H) m hm)) := by
  have : IrreducibleSpace (PrimeSpectrum H) :=
    CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace k (.of k H)
  obtain ⟨m', hm', hclosed, hsub⟩ :=
    exists_isClosed_range_projectiveOrbitMap_subset_closure (H := H) m hm
  exact ⟨m', hm', range_projectiveOrbitMap_eq_singleton_of_isClosed_of_isSolvable m' hm' hclosed,
    hsub⟩

/-- The closure of every projective orbit of a reduced connected solvable affine group contains
a line that is stable under every rational point of the group. -/
theorem exists_map_span_eq_span_mem_closure_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m) :
    ∃ (m' : M) (hm' : Module.IsUnimodular k m'),
      projectiveOrbitMap (H := H) m' hm' (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
          closure (Set.range (projectiveOrbitMap (H := H) m hm)) ∧
        ∀ g : WithConv (H →ₐ[k] k), (k ∙ m').map (basePointsRepresentation M g) = k ∙ m' := by
  have : IrreducibleSpace (PrimeSpectrum H) :=
    CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace k (.of k H)
  obtain ⟨m', hm', hclosed, hsub⟩ :=
    exists_isClosed_range_projectiveOrbitMap_subset_closure (H := H) m hm
  exact ⟨m', hm', hsub (Set.mem_range_self _),
    map_span_eq_span_of_isClosed_range_projectiveOrbitMap_of_isSolvable m' hm' hclosed⟩

/-- The closure of every projective orbit of a reduced connected solvable affine group contains
a line whose stabilizer is the whole group. -/
theorem exists_stabilizerHopfIdeal_span_eq_bot_mem_closure_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m) :
    ∃ (m' : M) (hm' : Module.IsUnimodular k m'),
      projectiveOrbitMap (H := H) m' hm' (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈
          closure (Set.range (projectiveOrbitMap (H := H) m hm)) ∧
        (k ∙ m').stabilizerHopfIdeal H = ⊥ := by
  obtain ⟨m', hm', hm'O, hline⟩ := exists_map_span_eq_span_mem_closure_of_isSolvable (H := H) m hm
  refine ⟨m', hm', hm'O, Submodule.stabilizerHopfIdeal_eq_bot_of_forall_basePointsRepresentation_mem
    _ fun g _ hx ↦ ?_⟩
  exact hline g ▸ Submodule.mem_map_of_mem hx

/-- **Borel fixed point theorem.** Let a reduced connected solvable affine group act on the
projective space of a finite-dimensional representation. A closed subset that is stable under
the rational translations and contains a line contains a point fixed by every rational
translation; this point is a line whose orbit is a single point. -/
theorem exists_projectivePointTranslation_eq_mem_of_isClosed_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m)
    {Z : Set (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))}
    (hZ : IsClosed Z)
    (hinvariant : ∀ g : WithConv (H →ₐ[k] k),
      Set.MapsTo (projectivePointTranslation (M := M) g).hom Z Z)
    (hmZ : projectiveOrbitMap (H := H) m hm
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z) :
    ∃ (m' : M) (hm' : Module.IsUnimodular k m'),
      projectiveOrbitMap (H := H) m' hm' (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z ∧
        ∀ g : WithConv (H →ₐ[k] k),
          (projectivePointTranslation (M := M) g).hom
              (projectiveOrbitMap (H := H) m' hm'
                (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H))) =
            projectiveOrbitMap (H := H) m' hm'
              (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) := by
  have : IrreducibleSpace (PrimeSpectrum H) :=
    CommHopfAlgCat.irreducibleSpace_primeSpectrum_of_connectedSpace k (.of k H)
  obtain ⟨m', hm', hclosed, hsub⟩ :=
    exists_isClosed_range_projectiveOrbitMap_subset_closure (H := H) m hm
  refine ⟨m', hm', closure_minimal
    ((range_projectiveOrbitMap_subset_iff_of_isClosed m hm hZ hinvariant).mpr hmZ) hZ
    (hsub (Set.mem_range_self _)), fun g ↦ ?_⟩
  have h := projectivePointTranslation_projectiveOrbitMap_kernelPoint g 1 m' hm'
  rw [mul_one] at h
  have h1 : (1 : WithConv (H →ₐ[k] k)).ofConv = Bialgebra.counitAlgHom k H := by
    simp [AlgHom.convOne_def]
  rw [h1] at h
  rw [h, projectiveOrbitMap_eq_identity_of_isClosed_of_isSolvable m' hm' hclosed]

/-- **Borel fixed point theorem**, linear form. A closed subset of projective space that is
stable under the rational translations of a reduced connected solvable affine group and
contains a line contains a line that is stable under every rational point of the group. -/
theorem exists_map_span_eq_span_mem_of_isClosed_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m)
    {Z : Set (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))}
    (hZ : IsClosed Z)
    (hinvariant : ∀ g : WithConv (H →ₐ[k] k),
      Set.MapsTo (projectivePointTranslation (M := M) g).hom Z Z)
    (hmZ : projectiveOrbitMap (H := H) m hm
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z) :
    ∃ (m' : M) (hm' : Module.IsUnimodular k m'),
      projectiveOrbitMap (H := H) m' hm' (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z ∧
        ∀ g : WithConv (H →ₐ[k] k), (k ∙ m').map (basePointsRepresentation M g) = k ∙ m' := by
  obtain ⟨m', hm', hm'O, hline⟩ := exists_map_span_eq_span_mem_closure_of_isSolvable (H := H) m hm
  exact ⟨m', hm', closure_minimal
    ((range_projectiveOrbitMap_subset_iff_of_isClosed m hm hZ hinvariant).mpr hmZ) hZ hm'O, hline⟩

/-- **Borel fixed point theorem**, stabilizer form. A closed subset of projective space that is
stable under the rational translations of a reduced connected solvable affine group and contains
a line contains a line whose stabilizer is the whole group. -/
theorem exists_stabilizerHopfIdeal_span_eq_bot_mem_of_isClosed_of_isSolvable
    (m : M) (hm : Module.IsUnimodular k m)
    {Z : Set (Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule k (Module.Dual k M)))}
    (hZ : IsClosed Z)
    (hinvariant : ∀ g : WithConv (H →ₐ[k] k),
      Set.MapsTo (projectivePointTranslation (M := M) g).hom Z Z)
    (hmZ : projectiveOrbitMap (H := H) m hm
      (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z) :
    ∃ (m' : M) (hm' : Module.IsUnimodular k m'),
      projectiveOrbitMap (H := H) m' hm' (AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)) ∈ Z ∧
        (k ∙ m').stabilizerHopfIdeal H = ⊥ := by
  obtain ⟨m', hm', hm'O, hstab⟩ :=
    exists_stabilizerHopfIdeal_span_eq_bot_mem_closure_of_isSolvable (H := H) m hm
  exact ⟨m', hm', closure_minimal
    ((range_projectiveOrbitMap_subset_iff_of_isClosed m hm hZ hinvariant).mpr hmZ) hZ hm'O, hstab⟩

end TauCeti.Comodule
