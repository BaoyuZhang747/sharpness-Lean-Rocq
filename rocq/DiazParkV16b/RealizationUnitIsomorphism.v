(** Invariance of the literal realization-unit comparison under a simplicial isomorphism. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialSet SimplicialSetYoneda SimplicialChains SimplicialChainsMaps
  ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws TopologicalCategory
  GeometricRealizationMaps SingularCohomology SingularChainComparison RealizationUnitChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialSet DPSimplicialYoneda DPSimplicialChains DPSimplicialChainMaps DPChainComplex
  DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPTopological DPGeometricRealizationMaps
  DPSingularCohomology DPSingularChainComparison DPRealizationUnitChains.
Module DPRealizationUnitIsomorphism.

Lemma simplicial_isomorphism_chains (R : pzRingType) (X Y : simplicial_set)
    (e : @isomorphism simplicial_category X Y) : quasi_isomorphism (chain_map_of R (iso_hom e)).
Proof.
apply: degreewise_bijective_quasi_isomorphism.
- move=> n x y hxy.
  have hk z : map_at R (iso_inv e) n (map_at R (iso_hom e) n z) = z.
    have he : nat_comp (iso_hom e) (iso_inv e) = nat_id X := iso_hom_inv e.
    rewrite -map_composition he; exact: map_identity.
  by rewrite -(hk x) -(hk y) hxy.
- move=> n y; exists (map_at R (iso_inv e) n y).
  change (map_at R (iso_hom e) n (map_at R (iso_inv e) n y) = y).
  have he : nat_comp (iso_inv e) (iso_hom e) = nat_id Y := iso_inv_hom e.
  rewrite -map_composition he; exact: map_identity.
Qed.

Theorem realization_unit_isomorphism (Real : realType) (R : pzRingType)
    (X Y : simplicial_set) (e : @isomorphism simplicial_category X Y)
    (hx : quasi_isomorphism (realization_unit_chains Real R X)) :
    quasi_isomorphism (realization_unit_chains Real R Y).
Proof.
apply: (@quasi_isomorphism_cancel_first R _ _ _ (chain_map_of R (iso_hom e))
  (realization_unit_chains Real R Y)); first exact: simplicial_isomorphism_chains.
apply: (@quasi_isomorphism_ext R _ _
  (chain_composition (realization_unit_chains Real R X)
    (singular_chain_map Real R (realization_map Real (iso_hom e))))).
- exact: realization_unit_naturality.
- apply: quasi_isomorphism_composition; first exact hx.
  exact (@singular_homeomorphism_quasi_isomorphism Real R _ _ (functor_iso (realization_functor Real) e)).
Qed.
End DPRealizationUnitIsomorphism.
