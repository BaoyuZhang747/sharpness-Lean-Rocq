(** The literal unit is a homology isomorphism on every arbitrary family of standard cells. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness HomologicalModuleIso
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainHomology ChainHomologyMaps ChainQuasiIsomorphism
  SimplicialSet SimplicialCopower SimplicialChains SingularCohomology GeometricRealizationCarrier
  RealizationUnitChains RealizationUnitStandardSimplex RealizationUnitCopower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomologicalModuleIso DPChainHomology DPChainHomologyMaps DPChainQuasiIsomorphism
  DPSimplicialSet DPSimplicialCopower DPRealizationUnitChains
  DPRealizationUnitStandardSimplex DPRealizationUnitCopower.
Module DPRealizationUnitStandardCopower.

Theorem standard_copower_unit_quasi_isomorphism (Real : realType) (R : pzRingType)
    (I : Type) d :
  quasi_isomorphism (realization_unit_chains Real R (copower I (standard_simplex d))).
Proof.
apply: (@realization_unit_copower_quasi_isomorphism Real R I (standard_simplex d)).
move=> n; split.
- exact: (module_iso_hom_injective (e := standard_unit_homology_iso Real R d n)).
- move=> y; exists (module_hom_fun (iso_inv (standard_unit_homology_iso Real R d n)) y).
  exact (@module_iso_inv_hom_apply R _ _ (standard_unit_homology_iso Real R d n) y).
Qed.

Definition standard_copower_unit_homology_iso (Real : realType) (R : pzRingType)
    (I : Type) d n :=
  @linear_bijection_iso R
    [the lmodType R of homology (DPSimplicialChains.chains R (copower I (standard_simplex d))) n]
    [the lmodType R of homology (DPSingularCohomology.singular_chains Real R
      (DPGeometricRealization.realization_space Real (copower I (standard_simplex d)))) n]
    (homology_map (realization_unit_chains Real R (copower I (standard_simplex d))) n)
    (proj1 (@standard_copower_unit_quasi_isomorphism Real R I d n))
    (proj2 (@standard_copower_unit_quasi_isomorphism Real R I d n)).

Theorem standard_copower_unit_homology_iso_hom (Real : realType) (R : pzRingType)
    (I : Type) d n q :
  module_hom_fun (iso_hom (@standard_copower_unit_homology_iso Real R I d n)) q =
    homology_map (realization_unit_chains Real R (copower I (standard_simplex d))) n q.
Proof. reflexivity. Qed.
End DPRealizationUnitStandardCopower.
