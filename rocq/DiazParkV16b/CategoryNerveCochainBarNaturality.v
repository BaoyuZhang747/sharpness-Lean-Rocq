(** Functor and coefficient naturality of the actual nerve/category-bar cochain equivalence. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps CategoryComplexIso BarPaths BarNaturality.
From DiazParkV16b Require Import SimplicialSet SimplicialCochains SimplicialCochainMaps
  CategoryNerve CategoryNervePaths CategoryNervePathsNaturality CategoryBarPullbackPaths
  CategoryBarPullbackConstant CategoryNerveCochainBarTerms CategoryNerveCochainBar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkBarPaths DiazParkBarNaturality
  DPSimplicialSet DPSimplicialCochains DPSimplicialCochainMaps DPCategoryNerve
  DPCategoryNervePathEquivalence DPCategoryNervePathNaturality DPCategoryBarPullback DPCategoryBarConstant
  DPCategoryNerveCochainBarTerms DPCategoryNerveCochainBar.
Local Open Scope ring_scope.

Module DPCategoryNerveCochainBarNaturality.
Section Functors.
Variable R : pzRingType.
Variable A : lmodType R.
Variables C D : category.
Variable F : functor C D.
Theorem nerve_bar_functor_naturality n a :
  cochain_map_at (nerve_bar_cochain_map C A) n (cochain_map_at (pull (nerve_map F) A) n a) =
    cochain_map_at (constant_bar_pullback A F) n (cochain_map_at (nerve_bar_cochain_map D A) n a).
Proof.
apply functional_extensionality_dep => x; apply functional_extensionality_dep => p.
change (a (functor_comp (path_nerve (existT _ x p)) F) =
  a (path_nerve (path_map F n (existT _ x p)))).
by rewrite path_nerve_map.
Qed.
Theorem bar_nerve_functor_naturality n a :
  cochain_map_at (pull (nerve_map F) A) n (cochain_map_at (bar_nerve_cochain_map D A) n a) =
    cochain_map_at (bar_nerve_cochain_map C A) n (cochain_map_at (constant_bar_pullback A F) n a).
Proof.
apply (can_inj (@nerve_bar_cochain_left R C A n)).
rewrite nerve_bar_functor_naturality !nerve_bar_cochain_right; reflexivity.
Qed.
Theorem nerve_bar_functor_cohomology n a :
  cohomology_map (nerve_bar_cochain_map C A) n (cohomology_map (pull (nerve_map F) A) n a) =
    cohomology_map (constant_bar_pullback A F) n (cohomology_map (nerve_bar_cochain_map D A) n a).
Proof.
symmetry; apply: cohomology_map_square.
move=> k x; symmetry; exact: nerve_bar_functor_naturality.
Qed.
End Functors.

Section Coefficients.
Variable R : pzRingType.
Variable C : category.
Variables A B : lmodType R.
Variable u : module_hom A B.
Definition constant_coefficient_trans : nat_trans (constant_coefficient R C A) (constant_coefficient R C B).
Proof.
refine (@Build_nat_trans (opposite C) (module_category R)
  (constant_coefficient R C A) (constant_coefficient R C B) (fun _ => u) _).
move=> x y f; apply module_hom_ext => a; reflexivity.
Defined.
Definition constant_bar_coefficient_map := bar_cochain_map constant_coefficient_trans.
Theorem nerve_bar_coefficient_naturality n a :
  cochain_map_at (nerve_bar_cochain_map C B) n
    (cochain_map_at (coefficient (nerve C) (module_hom_to_linear u)) n a) =
  cochain_map_at constant_bar_coefficient_map n (cochain_map_at (nerve_bar_cochain_map C A) n a).
Proof. apply functional_extensionality_dep => x; apply functional_extensionality_dep => p; reflexivity. Qed.
Theorem bar_nerve_coefficient_naturality n a :
  cochain_map_at (coefficient (nerve C) (module_hom_to_linear u)) n
    (cochain_map_at (bar_nerve_cochain_map C A) n a) =
  cochain_map_at (bar_nerve_cochain_map C B) n (cochain_map_at constant_bar_coefficient_map n a).
Proof.
apply (can_inj (@nerve_bar_cochain_left R C B n)).
rewrite nerve_bar_coefficient_naturality !nerve_bar_cochain_right; reflexivity.
Qed.
Theorem nerve_bar_coefficient_cohomology n a :
  cohomology_map (nerve_bar_cochain_map C B) n
    (cohomology_map (coefficient (nerve C) (module_hom_to_linear u)) n a) =
  cohomology_map constant_bar_coefficient_map n (cohomology_map (nerve_bar_cochain_map C A) n a).
Proof.
symmetry; apply: cohomology_map_square.
move=> k x; symmetry; exact: nerve_bar_coefficient_naturality.
Qed.
End Coefficients.
End DPCategoryNerveCochainBarNaturality.
