(** Objectwise actual unit comparisons assemble into a genuine natural isomorphism of coefficient diagrams. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryNaturalIso HomologicalCohomology HomologicalCohomologyMaps MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import SimplicialSet SimplicialSetYoneda SimplicialCohomologyFunctor
 SingularCohomology SingularCohomologyFunctor TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps
 ChainQuasiIsomorphism RealizationUnitChains RealizationUnitCochainComparison.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialSet DPSimplicialYoneda DPSimplicialCohomologyFunctor DPSingularCohomology DPSingularCohomologyFunctor
 DPTopological DPGeometricRealization DPGeometricRealizationMaps DPChainQuasiIsomorphism DPRealizationUnitChains DPRealizationUnitCochainComparison DiazParkCohomologyMaps.
Module DPRealizationUnitCohomologyDiagram.
Section Diagram.
Variable Real:realType.
Variable R:comPzRingType.
Variable A:lmodType R.
Variable C:category.
Variable F:functor C simplicial_category.
Variable n:nat.
Definition realized_cohomology_diagram :=
 functor_comp (functor_op (functor_comp F (realization_functor Real))) (singular_cohomology_functor Real A n).
Definition unit_cohomology_transformation : nat_trans realized_cohomology_diagram (simplicial_cohomology_diagram A n F).
Proof.
refine (@Build_nat_trans (opposite C) (module_category R) realized_cohomology_diagram (simplicial_cohomology_diagram A n F)
 (fun c=>module_hom_of_linear (cohomology_map (unit_pull Real A (fobj F c)) n)) _).
move=>c d f; apply module_hom_ext=>x; exact: unit_cohomology_natural.
Defined.
Variable hF:forall c, quasi_isomorphism (realization_unit_chains Real R (fobj F c)).
Definition unit_cohomology_nat_iso : @isomorphism (functor_category (opposite C) (module_category R))
 realized_cohomology_diagram (simplicial_cohomology_diagram A n F).
Proof.
refine (@nat_iso_of_components (opposite C) (module_category R) realized_cohomology_diagram (simplicial_cohomology_diagram A n F)
 (fun c=>@unit_cohomology_iso Real R A (fobj F c) (hF c) n) _).
move=>c d f; apply module_hom_ext=>x.
change (module_hom_fun (iso_hom (@unit_cohomology_iso Real R A (fobj F d) (hF d) n))
 (singular_cohomology_map Real (realization_map Real (fmap F f)) A n x)=
 cohomology_map (SimplicialCochainMaps.DPSimplicialCochainMaps.pull (fmap F f) A) n
 (module_hom_fun (iso_hom (@unit_cohomology_iso Real R A (fobj F c) (hF c) n)) x)).
rewrite !unit_cohomology_iso_forward; exact: unit_cohomology_natural.
Defined.
Lemma unit_cohomology_nat_iso_hom : iso_hom unit_cohomology_nat_iso=unit_cohomology_transformation.
Proof.
apply nat_trans_ext=>c; apply module_hom_ext=>x; exact: unit_cohomology_iso_forward.
Qed.
End Diagram.
End DPRealizationUnitCohomologyDiagram.
