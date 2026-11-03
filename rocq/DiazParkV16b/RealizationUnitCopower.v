(** The literal realization-unit comparison extends to arbitrary copowers.
    The singular comparison is proved from actual connected simplices. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryModules BarFreeModule HomologicalModuleIso.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps ChainQuasiIsomorphism
  ChainQuasiIsomorphismLaws SimplexCategoryTypes SimplicialSet SimplicialCopower SimplicialChains SimplicialChainsMaps
  SimplicialCopowerQuasiIso SingularSet SingularCohomology SingularCoproductComponents
  SingularCoproductChains SingularHomeomorphismChains TopologicalCategory
  GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationCopower
  GeometricRealizationSingularAdjunction RealizationUnitChains.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DiazParkHomologicalModuleIso
  DPChainComplex DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphism
  DPChainQuasiIsomorphismLaws DPSimplicialTypes DPSimplicialSet DPSimplicialCopower DPSimplicialChains DPSimplicialChainMaps
  DPSimplicialCopowerQuasiIso DPSingularSet DPSingularCohomology DPSingularCoproductComponents
  DPSingularCoproductChains DPSingularHomeomorphismChains DPTopological
  DPGeometricRealization DPGeometricRealizationMaps DPGeometricRealizationCopower
  DPGeometricRealizationSingularAdjunction DPRealizationUnitChains.

Module DPRealizationUnitCopower.
Section Copower.
Variable Real : realType.
Variable R : pzRingType.
Variable I : Type.
Variable X : simplicial_set.
Let F := chain_map_of R (@copower_map I X (singular_set Real (realization_space Real X))
  (realization_unit_map Real X)).
Let G := singular_copower_chain_map Real R I (realization_space Real X).
Let H := singular_chain_map Real R (copower_forward Real I X).

Lemma copower_unit_simplicial_square :
  nat_comp (realization_unit_map Real (copower I X))
    (singular_map Real (copower_forward Real I X)) =
  nat_comp (@copower_map I X (singular_set Real (realization_space Real X)) (realization_unit_map Real X))
    (singular_copower_map Real I (realization_space Real X)).
Proof.
apply: nat_trans_ext => n; apply: type_morphism_ext => [[i s]].
apply/continuousEP => t; exact: copower_forward_characteristic.
Qed.

Lemma copower_unit_square n (x : chain_term (chains R (copower I X)) n) :
  chain_map_at H n (chain_map_at (realization_unit_chains Real R (copower I X)) n x) =
    chain_map_at G n (chain_map_at F n x).
Proof.
change (map_at R (singular_map Real (copower_forward Real I X)) n
    (map_at R (realization_unit_map Real (copower I X)) n x) =
  map_at R (singular_copower_map Real I (realization_space Real X)) n
    (map_at R (@copower_map I X (singular_set Real (realization_space Real X))
      (realization_unit_map Real X)) n x)).
by rewrite -!map_composition copower_unit_simplicial_square.
Qed.

Lemma copower_forward_chains_quasi_isomorphism : quasi_isomorphism H.
Proof.
apply: degreewise_bijective_quasi_isomorphism.
- move=> n; exact: (can_inj (@singular_homeomorphism_forwardK Real R _ _
    (realization_copower_homeomorphism Real I X) n)).
- move=> n y; exists (chain_map_at (singular_chain_map Real R
    (iso_inv (realization_copower_homeomorphism Real I X))) n y).
  exact: singular_homeomorphism_inverseK.
Qed.

Theorem realization_unit_copower_quasi_isomorphism
    (hX : quasi_isomorphism (realization_unit_chains Real R X)) :
    quasi_isomorphism (realization_unit_chains Real R (copower I X)).
Proof.
apply: (@quasi_isomorphism_cancel_second R _ _ _ (realization_unit_chains Real R (copower I X)) H).
- exact: copower_forward_chains_quasi_isomorphism.
- apply: (@quasi_isomorphism_ext R _ _ (chain_composition F G)
    (chain_composition (realization_unit_chains Real R (copower I X)) H)).
  + move=> n x; symmetry; exact: copower_unit_square.
  + apply: quasi_isomorphism_composition.
    * apply: copower_map_quasi_isomorphism; exact hX.
    * apply: degreewise_bijective_quasi_isomorphism;
        [exact: singular_copower_chain_map_injective | exact: singular_copower_chain_map_surjective].
Qed.
End Copower.
End DPRealizationUnitCopower.
