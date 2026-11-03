(** The literal bar pullback is an isomorphism on cohomology whenever the
    actual induced augmented bar is exact. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleExactness
  CategoryEnoughProjectivesResolution CategoryEnoughProjectivesComparison CategoryDiagramHomLimit
  ProjectiveExtComplex ProjectiveExtIndependence ProjectiveExtBar CategoryComplexIso
  BarComplex BarResolutionTerms HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalModuleIso ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import CategoryBarPullback CategoryInducedBarTerms
  CategoryInducedBarDifferential CategoryInducedBarAugmentation CategoryInducedBarProjective
  CategoryInducedBarResolution CategoryInducedBarPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectiveResolutions DPProjectiveComparison DPProjectiveExt
  DPProjectiveExtIndependence DPProjectiveExtBar DiazParkBarComplex DiazParkBarResolutionTerms
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalModuleIso
  DPCategoryBarPullbackMaps.
Local Open Scope ring_scope.
Local Opaque module_quotient.

Section PullbackIso.
Variable R : comPzRingType.
Variables C D : category.
Variable q : functor C D.
Hypothesis augmentation_surjective : forall d (a : R^o),
  exists v, module_hom_fun (component (induced_bar_augmentation R q) d) v = a.
Hypothesis augmentation_exact : forall d (v : fobj (induced_bar_term R q 0%N) d),
  module_hom_fun (component (induced_bar_augmentation R q) d) v = 0 ->
  exists w, module_hom_fun (component (induced_bar_boundary R q 0%N) d) w = v.
Hypothesis successor_exact : forall n d (v : fobj (induced_bar_term R q n.+1) d),
  module_hom_fun (component (induced_bar_boundary R q n) d) v = 0 ->
  exists w, module_hom_fun (component (induced_bar_boundary R q n.+1) d) w = v.

Let P := @induced_bar_projective_resolution R C D q
  augmentation_surjective augmentation_exact successor_exact.
Let Q := @bar_projective_resolution R D.
Let f := @induced_bar_comparison_resolution R C D q
  augmentation_surjective augmentation_exact successor_exact.
Let g := projective_resolution_comparison Q P (nat_id (constant_regular_diagram R (opposite D))).
Variable M : module_codiagram R D.

Definition induced_bar_comparison_hom_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology (projective_hom_complex Q M) n]
    [the lmodType R of cohomology (projective_hom_complex P M) n].
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (cohomology_map (projective_hom_map M f) n))
  (module_hom_of_linear (cohomology_map (projective_hom_map M g) n)) _ _).
- apply module_hom_ext; intro z; exact: projective_hom_inverse.
- apply module_hom_ext; intro z; exact: projective_hom_inverse.
Defined.

Lemma induced_bar_pullback_cohomology_square n
    (z : cohomology (projective_hom_complex Q M) n) :
    module_hom_fun (iso_hom (@induced_bar_hom_cohomology_iso R C D q
      augmentation_surjective augmentation_exact successor_exact M n))
      (cohomology_map (projective_hom_map M f) n z) =
    cohomology_map (bar_pullback_cochain_map q M) n
      (module_hom_fun (iso_hom (bar_projective_cohomology_iso M n)) z).
Proof.
apply cohomology_map_square.
intros k a; exact: induced_bar_comparison_hom.
Qed.

Definition induced_bar_pullback_cohomology_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology (bar_complex M) n]
    [the lmodType R of cohomology (bar_complex (pullback_diagram q M)) n] :=
  module_iso_comp (iso_symm (bar_projective_cohomology_iso M n))
    (module_iso_comp (induced_bar_comparison_hom_iso n)
      (@induced_bar_hom_cohomology_iso R C D q
        augmentation_surjective augmentation_exact successor_exact M n)).

Theorem induced_bar_pullback_cohomology_iso_hom n (z : cohomology (bar_complex M) n) :
    module_hom_fun (iso_hom (induced_bar_pullback_cohomology_iso n)) z =
    cohomology_map (bar_pullback_cochain_map q M) n z.
Proof.
change (module_hom_fun (iso_hom (@induced_bar_hom_cohomology_iso R C D q
  augmentation_surjective augmentation_exact successor_exact M n))
  (cohomology_map (projective_hom_map M f) n
    (module_hom_fun (iso_inv (bar_projective_cohomology_iso M n)) z)) =
  cohomology_map (bar_pullback_cochain_map q M) n z).
by rewrite induced_bar_pullback_cohomology_square module_iso_inv_hom_apply.
Qed.
End PullbackIso.
