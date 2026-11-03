(** The actual realization-unit comparison for an empty simplicial set. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import BarFreeModule.
From DiazParkV16b Require Import SimplicialSet SimplicialChains SimplicialSkeletonAttachmentCover
  SimplicialSkeletonAttachmentStages ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws
  TopologicalSimplexBasic GeometricRealizationCarrier SingularSet SingularCohomology RealizationUnitChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPSimplicialSet DPSimplicialChains DPSimplicialAttachmentCover
  DPSimplicialAttachmentStages DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws
  DPTopologicalSimplex DPGeometricRealization DPSingularSet DPSingularCohomology DPRealizationUnitChains.
Local Open Scope ring_scope.
Module DPRealizationUnitEmpty.

Lemma empty_free_module_unique (R : pzRingType) (A : Type) (hA : A -> False)
    (x y : free_module R A) : x = y.
Proof. apply: free_coefficient_ext => a; exfalso; exact: hA a. Qed.

Section Empty.
Variable Real : realType.
Variable R : pzRingType.
Variable X : simplicial_set.
Variable hx : forall n, DPSimplicialSet.simplex X n -> False.

Lemma empty_realization_point (z : realization Real X) : False.
Proof.
have [[[n x] t] _] := @realization_class_surjective Real X z.
exact: hx x.
Qed.

Lemma empty_singular_simplex n (s : DPSimplicialSet.simplex (singular_set Real (realization_space Real X)) n) : False.
Proof. exact: (empty_realization_point (s (@vertex Real n ord0))). Qed.

Theorem empty_realization_unit_quasi_isomorphism : quasi_isomorphism (realization_unit_chains Real R X).
Proof.
apply: degreewise_bijective_quasi_isomorphism.
- move=> n x y _; exact: (empty_free_module_unique (@hx n)).
- move=> n y; exists 0.
  exact: (empty_free_module_unique (@empty_singular_simplex n)).
Qed.
End Empty.

Theorem stage_zero_unit_quasi_isomorphism (Real : realType) (R : pzRingType) (X : simplicial_set) :
  quasi_isomorphism (realization_unit_chains Real R (stage_set X 0)).
Proof.
apply: empty_realization_unit_quasi_isomorphism => n [x hx].
have [m [y [f [hm _]]]] := hx.
by move: hm; rewrite ltn0.
Qed.
End DPRealizationUnitEmpty.
