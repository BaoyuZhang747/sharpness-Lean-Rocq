(** An actual adjunction of categories identifies native singular cohomology
    by the literal pullback along its left adjoint. *)
From mathcomp Require Import all_boot all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryAdjunction CategoryModules
  CategoryModuleExactness HomologicalModuleIso.
From DiazParkV16b Require Import CategoryNerve CategoryConstantCohomology
  SingularCohomology SingularCohomologyFunctor GeometricRealizationMaps
  RealizationNerveCohomology RealizationNerveCohomologyUnconditional.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomologicalModuleIso DPCategoryNerve DPSingularCohomology
  DPSingularCohomologyFunctor DPGeometricRealizationMaps
  DPRealizationNerveCohomology DPRealizationNerveCohomologyUnconditional.

Module DPBLOCohomologyAdjunction.
Section Adjunction.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variables C D : category.
Variable F : functor C D.
Variable G : functor D C.
Variable a : adjunction F G.
Variable n : nat.

Definition native_value (T : category) :=
  fobj (singular_cohomology_functor Real A n) (classifying_space Real T).

Definition native_pull_iso : @isomorphism (module_category R)
    (native_value D) (native_value C) :=
  module_iso_comp (comparison_iso_unconditional Real A D n)
    (module_iso_comp (iso_symm (DPCategoryConstantCohomology.adjunction_iso A a n))
      (iso_symm (comparison_iso_unconditional Real A C n))).

Lemma native_pull_iso_forward (x : native_value D) :
    module_hom_fun (iso_hom native_pull_iso) x =
    singular_cohomology_map Real (realization_map Real (nerve_map F)) A n x.
Proof.
apply (@module_iso_hom_injective R _ _ (comparison_iso_unconditional Real A C n)).
change (module_hom_fun (iso_hom (comparison_iso_unconditional Real A C n))
  (module_hom_fun (iso_inv (comparison_iso_unconditional Real A C n))
    (DPCategoryConstantCohomology.pull A F n
      (module_hom_fun (iso_hom (comparison_iso_unconditional Real A D n)) x))) =
  module_hom_fun (iso_hom (comparison_iso_unconditional Real A C n))
    (singular_cohomology_map Real (realization_map Real (nerve_map F)) A n x)).
rewrite module_iso_inv_hom_apply.
symmetry; exact: comparison_iso_unconditional_natural.
Qed.
End Adjunction.
End DPBLOCohomologyAdjunction.
