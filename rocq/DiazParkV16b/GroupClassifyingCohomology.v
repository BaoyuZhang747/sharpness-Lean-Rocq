(** Actual classifying spaces of finite groups and unconditional native group cohomology. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  CategoryModuleExactness HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps BarPaths
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import SimplexCategoryTypes SimplicialSet CategoryNerve CategoryNervePaths
  CategoryConstantCohomology CategoryNerveCochainBarGroup GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyCoefficients SingularCohomology TopologicalCategory
  GeometricRealizationMaps GeometricRealizationSingularAdjunction
  RealizationNerveCohomology RealizationNerveCohomologyUnconditional.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkBarPaths
  DPSimplicialTypes DPSimplicialSet DPCategoryNerve DPCategoryNervePathEquivalence
  DPCategoryNerveCochainBarGroup DPGroupCohomology DPGroupCohomologyFunctor
  DPSingularCohomology DPTopological DPGeometricRealizationMaps DPGeometricRealizationSingularAdjunction
  DPRealizationNerveCohomology DPRealizationNerveCohomologyUnconditional.

Module DPGroupClassifyingCohomology.
Section Spaces.
Variable Real : realType.
Definition group_classifying_space (G : finGroupType) : topologicalType := classifying_space Real (group_category G).
Definition group_classifying_map (G H : finGroupType) (f : {morphism [set: G] >-> H}) :
  hom topological_category (group_classifying_space G) (group_classifying_space H) :=
  realization_map Real (nerve_map (group_functor f)).

Theorem group_classifying_map_identity (G : finGroupType) :
  group_classifying_map (group_hom_identity G) = @identity topological_category (group_classifying_space G).
Proof.
rewrite /group_classifying_map group_functor_identity.
have e : nerve_map (functor_id (group_category G)) = nat_id (nerve (group_category G)).
  apply nat_trans_ext => n; apply type_morphism_ext => s; exact: nerve_map_identity.
by rewrite e realization_map_identity.
Qed.
Theorem group_classifying_map_composition (G H K : finGroupType)
  (f : {morphism [set: G] >-> H}) (g : {morphism [set: H] >-> K}) :
  group_classifying_map (group_hom_comp f g) = compose (group_classifying_map f) (group_classifying_map g).
Proof.
rewrite /group_classifying_map group_functor_composition.
have e : nerve_map (functor_comp (group_functor f) (group_functor g)) =
    nat_comp (nerve_map (group_functor f)) (nerve_map (group_functor g)).
  apply nat_trans_ext => n; apply type_morphism_ext => s; exact: nerve_map_compose.
by rewrite e realization_map_composition.
Qed.
End Spaces.

Section Comparison.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Definition group_comparison_cochain (G : finGroupType) :
  cochain_map (singular_cochains Real (group_classifying_space Real G) A) (DPGroupCohomology.complex R G A) :=
  comparison_cochain Real A (group_category G).
Definition group_comparison_iso (G : finGroupType) n : @isomorphism (module_category R)
  [the lmodType R of singular_cohomology Real (group_classifying_space Real G) A n]
  (DPGroupCohomology.value R G A n) := comparison_iso_unconditional Real A (group_category G) n.

Theorem group_comparison_iso_forward (G : finGroupType) n x :
  module_hom_fun (iso_hom (group_comparison_iso G n)) x = cohomology_map (group_comparison_cochain G) n x.
Proof. exact: comparison_iso_unconditional_forward. Qed.
Theorem group_comparison_characteristic_formula (G : finGroupType) n
  (a : cochain_term (singular_cochains Real (group_classifying_space Real G) A) n)
  c (p : @path_from (group_category G) n c) :
  cochain_map_at (group_comparison_cochain G) n a c p =
  a (component (realization_unit_map Real (nerve (group_category G))) n (path_nerve (existT _ c p))).
Proof. reflexivity. Qed.

Theorem group_comparison_pull_cochain (G H : finGroupType)
  (f : {morphism [set: G] >-> H}) n x :
  cochain_map_at (group_comparison_cochain G) n
    (cochain_map_at (singular_pullback Real (group_classifying_map Real f) A) n x) =
  cochain_map_at (DPGroupCohomologyPullback.pull_cochain A f) n
    (cochain_map_at (group_comparison_cochain H) n x).
Proof. exact: comparison_cochain_natural. Qed.

Theorem group_comparison_pull (G H : finGroupType)
  (f : {morphism [set: G] >-> H}) n x :
  module_hom_fun (iso_hom (group_comparison_iso G n))
    (singular_cohomology_map Real (group_classifying_map Real f) A n x) =
  module_hom_fun (DPGroupCohomologyPullback.pull A f n)
    (module_hom_fun (iso_hom (group_comparison_iso H n)) x).
Proof. exact: comparison_iso_unconditional_natural. Qed.

Theorem group_comparison_inverse_pull (G H : finGroupType)
  (f : {morphism [set: G] >-> H}) n (x : DPGroupCohomology.value R H A n) :
  singular_cohomology_map Real (group_classifying_map Real f) A n
    (module_hom_fun (iso_inv (group_comparison_iso H n)) x) =
  module_hom_fun (iso_inv (group_comparison_iso G n))
    (module_hom_fun (DPGroupCohomologyPullback.pull A f n) x).
Proof.
apply (@module_iso_hom_injective R _ _ (group_comparison_iso G n)).
by rewrite group_comparison_pull !module_iso_inv_hom_apply.
Qed.
End Comparison.

Section Coefficients.
Variable Real : realType.
Variable R : comPzRingType.
Variable G : finGroupType.
Variables A B : lmodType R.
Variable u : module_hom A B.

Theorem group_comparison_coefficient_cochain n
  (x : cochain_term (singular_cochains Real (group_classifying_space Real G) A) n) :
  cochain_map_at (group_comparison_cochain Real B G) n
    (cochain_map_at (singular_coefficient_map Real (group_classifying_space Real G) (module_hom_to_linear u)) n x) =
  cochain_map_at (DPGroupCohomologyCoefficients.coefficient_cochain_map G u) n
    (cochain_map_at (group_comparison_cochain Real A G) n x).
Proof. exact: comparison_cochain_coefficient. Qed.

Theorem group_comparison_coefficient n
  (x : singular_cohomology Real (group_classifying_space Real G) A n) :
  module_hom_fun (iso_hom (group_comparison_iso Real B G n))
    (cohomology_map (singular_coefficient_map Real (group_classifying_space Real G) (module_hom_to_linear u)) n x) =
  module_hom_fun (DPGroupCohomologyCoefficients.coefficient_map G u n)
    (module_hom_fun (iso_hom (group_comparison_iso Real A G n)) x).
Proof. exact: comparison_iso_unconditional_coefficient. Qed.

Theorem group_comparison_inverse_coefficient n (x : DPGroupCohomology.value R G A n) :
  cohomology_map (singular_coefficient_map Real (group_classifying_space Real G) (module_hom_to_linear u)) n
    (module_hom_fun (iso_inv (group_comparison_iso Real A G n)) x) =
  module_hom_fun (iso_inv (group_comparison_iso Real B G n))
    (module_hom_fun (DPGroupCohomologyCoefficients.coefficient_map G u n) x).
Proof.
apply (@module_iso_hom_injective R _ _ (group_comparison_iso Real B G n)).
by rewrite group_comparison_coefficient !module_iso_inv_hom_apply.
Qed.
End Coefficients.
End DPGroupClassifyingCohomology.
