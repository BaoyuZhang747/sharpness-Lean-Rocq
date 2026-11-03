(** Actual realization transports a native simplicial chain quasi-isomorphism to singular cohomology pullback. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import SimplicialSet SimplicialChainsMaps SimplicialCochains SimplicialCochainMaps
  SimplicialCochainQuasiIso CategoryNerve ChainQuasiIsomorphism
  SingularCohomology GeometricRealizationCarrier GeometricRealizationMaps
  RealizationUnitCochainComparison RealizationUnitComparison RealizationNerveCohomology.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalModuleIso
  DPSimplicialSet DPSimplicialChainMaps DPSimplicialCochains DPSimplicialCochainMaps DPSimplicialCochainQuasiIso
  DPCategoryNerve DPChainQuasiIsomorphism DPSingularCohomology DPGeometricRealization DPGeometricRealizationMaps
  DPRealizationUnitCochainComparison DPRealizationUnitComparison DPRealizationNerveCohomology.

Module DPRealizationFunctorCohomology.
Section Simplicial.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variables X Y : simplicial_set.
Variable f : simplicial_map X Y.
Variable hf : quasi_isomorphism (chain_map_of R f).

Definition realization_pull_cohomology_iso n : @isomorphism (module_category R)
  [the lmodType R of singular_cohomology Real (realization_space Real Y) A n]
  [the lmodType R of singular_cohomology Real (realization_space Real X) A n] :=
  module_iso_comp
    (@unit_cohomology_iso Real R A Y (realization_unit_quasi_isomorphism Real R Y) n)
    (module_iso_comp (@pull_cohomology_iso R A X Y f hf n)
      (iso_symm (@unit_cohomology_iso Real R A X (realization_unit_quasi_isomorphism Real R X) n))).

Theorem realization_pull_cohomology_iso_forward n
  (x : singular_cohomology Real (realization_space Real Y) A n) :
  module_hom_fun (iso_hom (realization_pull_cohomology_iso n)) x =
  singular_cohomology_map Real (realization_map Real f) A n x.
Proof.
apply (@module_iso_hom_injective R _ _
  (@unit_cohomology_iso Real R A X (realization_unit_quasi_isomorphism Real R X) n)).
change (module_hom_fun (iso_hom (@unit_cohomology_iso Real R A X (realization_unit_quasi_isomorphism Real R X) n))
  (module_hom_fun (iso_inv (@unit_cohomology_iso Real R A X (realization_unit_quasi_isomorphism Real R X) n))
    (module_hom_fun (iso_hom (@pull_cohomology_iso R A X Y f hf n))
      (module_hom_fun (iso_hom (@unit_cohomology_iso Real R A Y (realization_unit_quasi_isomorphism Real R Y) n)) x))) =
  module_hom_fun (iso_hom (@unit_cohomology_iso Real R A X (realization_unit_quasi_isomorphism Real R X) n))
    (singular_cohomology_map Real (realization_map Real f) A n x)).
rewrite module_iso_inv_hom_apply pull_cohomology_iso_forward !unit_cohomology_iso_forward.
symmetry; exact: unit_cohomology_natural.
Qed.

Theorem realization_pull_cohomology_injective n :
  injective (singular_cohomology_map Real (realization_map Real f) A n).
Proof.
move=> x y h; apply (@module_iso_hom_injective R _ _ (realization_pull_cohomology_iso n)).
by rewrite !realization_pull_cohomology_iso_forward.
Qed.
Theorem realization_pull_cohomology_surjective n
  (x : singular_cohomology Real (realization_space Real X) A n) :
  exists y, singular_cohomology_map Real (realization_map Real f) A n y = x.
Proof.
exists (module_hom_fun (iso_inv (realization_pull_cohomology_iso n)) x).
rewrite -realization_pull_cohomology_iso_forward; exact: module_iso_inv_hom_apply.
Qed.
End Simplicial.

Section Categories.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variables C D : category.
Variable F : functor C D.
Variable hF : quasi_isomorphism (chain_map_of R (nerve_map F)).
Definition classifying_functor_cohomology_iso n :=
  @realization_pull_cohomology_iso Real R A (nerve C) (nerve D) (nerve_map F) hF n.
Theorem classifying_functor_cohomology_iso_forward n
  (x : singular_cohomology Real (classifying_space Real D) A n) :
  module_hom_fun (iso_hom (classifying_functor_cohomology_iso n)) x =
  singular_cohomology_map Real (realization_map Real (nerve_map F)) A n x.
Proof. exact: realization_pull_cohomology_iso_forward. Qed.
End Categories.
End DPRealizationFunctorCohomology.
