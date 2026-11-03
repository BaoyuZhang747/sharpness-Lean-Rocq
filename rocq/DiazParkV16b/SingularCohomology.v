(** Actual singular chains, function cochains, and quotient cohomology. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category CategoryModules HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps.
From DiazParkV16b Require Import TopologicalCategory TopologicalSimplexOrdinal SingularSet SimplicialChains
  SimplicialChainsMaps SimplicialCochains SimplicialCochainMaps ChainDualCochain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularSet.

Module DPSingularCohomology.
Section Singular.
Variable Real : realType.
Variable R : pzRingType.

Definition singular_chains (X : topologicalType) :=
  DPSimplicialChains.chains R (singular_set Real X).
Definition singular_chain_map (X Y : topologicalType)
    (f : hom topological_category X Y) :=
  DPSimplicialChainMaps.chain_map_of R (singular_map Real f).

Definition singular_cochains (X : topologicalType) (A : lmodType R) :=
  DPSimplicialCochains.complex (singular_set Real X) A.
Definition singular_cohomology (X : topologicalType) (A : lmodType R) n :=
  DiazParkCohomology.cohomology (singular_cochains X A) n.

Definition singular_pullback (X Y : topologicalType)
    (f : hom topological_category X Y) (A : lmodType R) :=
  DPSimplicialCochainMaps.pull (singular_map Real f) A.
Definition singular_cohomology_map (X Y : topologicalType)
    (f : hom topological_category X Y) (A : lmodType R) n :=
  DiazParkCohomologyMaps.cohomology_map (singular_pullback f A) n.

Lemma singular_pullback_at (X Y : topologicalType)
    (f : hom topological_category X Y) (A : lmodType R) n
    (a : DiazParkHomological.cochain_term (singular_cochains Y A) n)
    (s : hom topological_category
      (fobj (DPTopologicalSimplexOrdinal.topological_simplex_functor Real) n) X) :
  DiazParkHomological.cochain_map_at (singular_pullback f A) n a s = a (compose s f).
Proof. reflexivity. Qed.

Definition singular_coefficient_map (X : topologicalType)
    (A B : lmodType R) (u : {linear A -> B}) :=
  DPSimplicialCochainMaps.coefficient (singular_set Real X) u.
End Singular.

Definition singular_dual_cohomology_iso (Real : realType) (R : comPzRingType)
    (X : topologicalType) (A : lmodType R) n :=
  DPSimplicialCochains.dual_function_cohomology_iso (singular_set Real X) A n.
End DPSingularCohomology.
