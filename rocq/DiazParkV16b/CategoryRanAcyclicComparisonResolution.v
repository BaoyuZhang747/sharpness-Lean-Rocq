(** The actual Ran image of an injective resolution is an augmented injective
    resolution when the chosen coefficients have positive comma acyclicity.
    Degree zero is retained by the actual augmentation. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryModuleLinear CategoryModuleExactness CategoryModuleLimits
  CategoryModuleLimitFunctor CategoryInjectives CategoryComma CategoryStructured
  CategoryModuleRightKan CategoryModuleRightKanLimits
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalDiagramInjectives
  HomologicalDiagramLimits HomologicalModuleIso
  CategoryInjectiveResolution CategoryEnoughInjectives CategoryResolutionTransport
  CategoryResolutionIndependence CategoryDerivedAdjunction CategoryDerivedTransport
  CategoryRanResolution CategoryComplexIso CategoryDerivedLimits CategoryFiberVanishing
  BarInjectiveDegreeZero.
From DiazParkV16b Require Import CategoryRanAcyclicComparisonComma.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkBarInjectiveDegreeZero.
Local Open Scope ring_scope.
Local Opaque chosen_injective_resolution module_quotient linear_preimage linear_kernel linear_image.

Definition ran_comma_positive_acyclic (R : pzRingType) {C D : category}
    (r : functor C D) (F : module_diagram R C) : Prop :=
  forall d n (v : derived_limit R (functor_comp (structured_projection r d) F) n.+1), v = 0.

Arguments ran_comma_positive_acyclic R {C D} r F.

Section ImageResolution.
Variable R : pzRingType.
Variables C D : category.
Variable r : functor C D.
Variable F : module_diagram R C.
Variable J : injective_resolution F.

Definition ran_comma_restricted_resolution (d : D) :
    injective_resolution (functor_comp (structured_projection r d) F) :=
  @mapped_injective_resolution R C (structured_category r d)
    (precomposition (module_category R) (structured_projection r d))
    (@module_restriction_preserves_zero R (structured_category r d) C (structured_projection r d))
    (@module_restriction_preserves_exact R (structured_category r d) C (structured_projection r d))
    (@module_restriction_preserves_injections R (structured_category r d) C (structured_projection r d))
    (fun M => ran_comma_restriction_preserves_injectives R r d M) F J.

Definition ran_image_resolution_complex : @diagram_complex R D :=
  mapped_diagram_complex (@module_ran_preserves_zero R C D r)
    (injective_resolution_complex J).

Definition ran_image_comma_term_iso d n : @isomorphism (module_category R)
    (cochain_term (diagram_evaluation_complex ran_image_resolution_complex d) n)
    (cochain_term (limit_complex
      (injective_resolution_complex (ran_comma_restricted_resolution d))) n) := iso_refl _.

Lemma ran_image_comma_term_commutes d n v :
    cochain_d (limit_complex (injective_resolution_complex
      (ran_comma_restricted_resolution d))) n
      (module_hom_fun (iso_hom (ran_image_comma_term_iso d n)) v) =
    module_hom_fun (iso_hom (ran_image_comma_term_iso d n.+1))
      (cochain_d (diagram_evaluation_complex ran_image_resolution_complex d) n v).
Proof. reflexivity. Qed.

Definition ran_image_comma_cohomology_iso d n : @isomorphism (module_category R)
    [the lmodType R of cohomology
      (diagram_evaluation_complex ran_image_resolution_complex d) n]
    (resolution_cohomology (ran_comma_restricted_resolution d) n) :=
  term_iso_cohomology_iso (@ran_image_comma_term_commutes d) n.

Definition ran_image_augmentation : nat_trans (fobj (module_ran R r) F)
    (diagram_term ran_image_resolution_complex 0%N) :=
  fmap (module_ran R r) (injective_resolution_augmentation J).

Lemma ran_image_augmentation_injective d :
    injective (module_hom_fun (component ran_image_augmentation d)).
Proof.
apply module_ran_preserves_injections.
exact: injective_resolution_augmentation_injective.
Qed.

Lemma ran_image_augmentation_zero d (v : fobj (fobj (module_ran R r) F) d) :
    module_hom_fun (component (diagram_d ran_image_resolution_complex 0%N) d)
      (module_hom_fun (component ran_image_augmentation d) v) = 0.
Proof.
exact (@diagram_functor_composite_zero R C D (module_ran R r)
  (@module_ran_preserves_zero R C D r) _ _ _
  (injective_resolution_augmentation J) (diagram_d (injective_resolution_complex J) 0%N)
  (injective_resolution_augmentation_zero J) d v).
Qed.

Lemma ran_image_exact_zero d
    (v : fobj (diagram_term ran_image_resolution_complex 0%N) d) :
    module_hom_fun (component (diagram_d ran_image_resolution_complex 0%N) d) v = 0 <->
    exists u, module_hom_fun (component ran_image_augmentation d) u = v.
Proof.
split.
- intro hv.
  pose (z := @cycle_of_cocycle R
    (limit_complex (injective_resolution_complex (ran_comma_restricted_resolution d)))
    0%N v hv).
  exists (@zero_cycle_limit R _ _ (ran_comma_restricted_resolution d) z).
  exact (congr1 (@submodule_val R _ _)
    (@zero_limit_cycle_inverse R _ _ (ran_comma_restricted_resolution d) z)).
- intros [u <-]; exact: ran_image_augmentation_zero.
Qed.

Hypothesis hF : ran_comma_positive_acyclic R r F.

Lemma ran_comma_restricted_positive_zero d n
    (v : resolution_cohomology (ran_comma_restricted_resolution d) n.+1) : v = 0.
Proof.
pose (e := derived_limit_resolution_iso (ran_comma_restricted_resolution d) n.+1).
transitivity (module_hom_fun (iso_hom e) (module_hom_fun (iso_inv e) v)).
- symmetry; exact: module_iso_inv_hom_apply.
- have hz := @hF d n (module_hom_fun (iso_inv e) v).
  rewrite hz; exact: module_hom_zero.
Qed.

Lemma ran_image_positive_zero d n
    (v : cohomology (diagram_evaluation_complex ran_image_resolution_complex d) n.+1) : v = 0.
Proof.
apply (@module_iso_hom_injective R _ _ (ran_image_comma_cohomology_iso d n.+1)).
rewrite module_hom_zero; exact: ran_comma_restricted_positive_zero.
Qed.

Lemma ran_image_exact_successor n d
    (v : fobj (diagram_term ran_image_resolution_complex n.+1) d) :
    module_hom_fun (component (diagram_d ran_image_resolution_complex n.+1) d) v = 0 ->
    exists u, module_hom_fun (component (diagram_d ran_image_resolution_complex n) d) u = v.
Proof.
exact (proj1 (cohomology_zero_iff
  (diagram_evaluation_complex ran_image_resolution_complex d) n.+1)
  (@ran_image_positive_zero d n) v).
Qed.

Definition ran_acyclic_injective_resolution : injective_resolution (fobj (module_ran R r) F).
Proof.
refine (@Build_injective_resolution R D (fobj (module_ran R r) F)
  ran_image_resolution_complex ran_image_augmentation _
  ran_image_augmentation_injective ran_image_augmentation_zero
  ran_image_exact_zero ran_image_exact_successor).
intro n; apply module_ran_preserves_injectives.
exact: injective_resolution_term_injective.
Defined.
End ImageResolution.

Arguments ran_comma_restricted_resolution R {C D} r {F} J d.
Arguments ran_image_resolution_complex R {C D} r {F} J.
Arguments ran_acyclic_injective_resolution R {C D} r {F} J hF.
