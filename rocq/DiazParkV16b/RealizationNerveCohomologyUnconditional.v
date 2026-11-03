(** Unconditional singular/classifying-space comparison with actual category cohomology. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryComplexIso
  HomologicalComplex HomologicalMaps HomologicalCohomology HomologicalCohomologyMaps BarPaths.
From DiazParkV16b Require Import SimplicialSet SimplicialCochains SimplicialCochainMaps CategoryNerve
  CategoryNervePaths CategoryConstantCohomology CategoryBarPullbackConstant CategoryNerveCochainBar
  CategoryNerveCochainBarNaturality SingularCohomology TopologicalCategory GeometricRealizationMaps
  GeometricRealizationSingularAdjunction RealizationUnitCochainComparison RealizationUnitComparison
  RealizationNerveCohomology.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology DiazParkCohomologyMaps DiazParkBarPaths
  DPSimplicialSet DPSimplicialCochainMaps DPCategoryNerve DPCategoryNervePathEquivalence
  DPCategoryBarConstant DPCategoryNerveCochainBar DPCategoryNerveCochainBarNaturality
  DPSingularCohomology DPTopological DPGeometricRealizationMaps DPGeometricRealizationSingularAdjunction
  DPRealizationUnitCochainComparison DPRealizationUnitComparison DPRealizationNerveCohomology.

Module DPRealizationNerveCohomologyUnconditional.
Section Comparison.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.

Definition comparison_iso_unconditional (C : category) n :=
  @comparison_iso Real R A C (realization_unit_quasi_isomorphism Real R (nerve C)) n.

Theorem comparison_iso_unconditional_forward (C : category) n x :
  module_hom_fun (iso_hom (comparison_iso_unconditional C n)) x =
  cohomology_map (comparison_cochain Real A C) n x.
Proof. exact: comparison_iso_forward. Qed.

Theorem comparison_characteristic_formula (C : category) n
  (a : cochain_term (singular_cochains Real (classifying_space Real C) A) n)
  c (p : @path_from C n c) :
  cochain_map_at (comparison_cochain Real A C) n a c p =
  a (component (realization_unit_map Real (nerve C)) n (path_nerve (existT _ c p))).
Proof. reflexivity. Qed.

Theorem comparison_iso_unconditional_natural (C D : category) (F : functor C D) n x :
  module_hom_fun (iso_hom (comparison_iso_unconditional C n))
    (singular_cohomology_map Real (realization_map Real (nerve_map F)) A n x) =
  module_hom_fun (DPCategoryConstantCohomology.pull A F n)
    (module_hom_fun (iso_hom (comparison_iso_unconditional D n)) x).
Proof. rewrite !comparison_iso_unconditional_forward; exact: comparison_cohomology_natural. Qed.
End Comparison.

Section Coefficients.
Variable Real : realType.
Variable R : comPzRingType.
Variable C : category.
Variables A B : lmodType R.
Variable u : module_hom A B.

Theorem comparison_cochain_coefficient n
  (x : cochain_term (singular_cochains Real (classifying_space Real C) A) n) :
  cochain_map_at (comparison_cochain Real B C) n
    (cochain_map_at (singular_coefficient_map Real (classifying_space Real C) (module_hom_to_linear u)) n x) =
  cochain_map_at (constant_bar_coefficient_map C u) n
    (cochain_map_at (comparison_cochain Real A C) n x).
Proof.
change (cochain_map_at (nerve_bar_cochain_map C B) n
  (cochain_map_at (unit_pull Real B (nerve C)) n
    (cochain_map_at (singular_coefficient_map Real (classifying_space Real C) (module_hom_to_linear u)) n x)) =
  cochain_map_at (constant_bar_coefficient_map C u) n
    (cochain_map_at (nerve_bar_cochain_map C A) n (cochain_map_at (unit_pull Real A (nerve C)) n x))).
rewrite -unit_pull_coefficient; exact: nerve_bar_coefficient_naturality.
Qed.

Theorem comparison_cohomology_coefficient n
  (x : singular_cohomology Real (classifying_space Real C) A n) :
  cohomology_map (comparison_cochain Real B C) n
    (cohomology_map (singular_coefficient_map Real (classifying_space Real C) (module_hom_to_linear u)) n x) =
  cohomology_map (constant_bar_coefficient_map C u) n
    (cohomology_map (comparison_cochain Real A C) n x).
Proof.
exact (@cohomology_map_square R _ _ _ _
  (singular_coefficient_map Real (classifying_space Real C) (module_hom_to_linear u))
  (constant_bar_coefficient_map C u) (comparison_cochain Real A C) (comparison_cochain Real B C)
  comparison_cochain_coefficient n x).
Qed.

Theorem comparison_iso_unconditional_coefficient n
  (x : singular_cohomology Real (classifying_space Real C) A n) :
  module_hom_fun (iso_hom (comparison_iso_unconditional Real B C n))
    (cohomology_map (singular_coefficient_map Real (classifying_space Real C) (module_hom_to_linear u)) n x) =
  cohomology_map (constant_bar_coefficient_map C u) n
    (module_hom_fun (iso_hom (comparison_iso_unconditional Real A C n)) x).
Proof. rewrite !comparison_iso_unconditional_forward; exact: comparison_cohomology_coefficient. Qed.
End Coefficients.
End DPRealizationNerveCohomologyUnconditional.
