(** Spectral-sequence-free fiber vanishing for genuine derived limits.
    A chosen injective resolution restricts to an injective resolution on
    every fiber by the actual exact fiber Lan. Its right Kan image is an
    exact complex of injectives, including degree zero, and hence splits. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryModuleLinear CategoryModuleExactness CategoryModuleLimits
  CategoryModuleLimitFunctor CategoryInjectives CategoryFibration CategoryFiberLan
  CategoryModuleFiberKan CategoryModuleRightKan CategoryModuleRightKanLimits
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalDiagramInjectives HomologicalDiagramLimits
  CategoryInjectiveResolution CategoryEnoughInjectives CategoryResolutionTransport
  CategoryResolutionIndependence CategoryDerivedAdjunction CategoryDerivedTransport
  CategoryRanResolution CategoryComplexIso CategoryDerivedLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology.
Local Open Scope ring_scope.
Local Opaque chosen_injective_resolution module_quotient linear_preimage linear_kernel linear_image.

Definition diagram_evaluation_complex {R : pzRingType} {C : category}
    (K : @diagram_complex R C) (x : C) : @cochain_complex R :=
  @CochainComplex R (fun n => fobj (diagram_term K n) x)
    (fun n => module_hom_to_linear (component (diagram_d K n) x))
    (fun n v => @diagram_d2 R C K n x v).

Section FiberVanishing.
Variable R : pzRingType.
Variables C D : category.
Variable p : functor C D.
Variable hp : fibration p.
Variable F : module_diagram R C.
Variable J : injective_resolution F.

Definition fiber_restricted_resolution (b : D) :
    injective_resolution (functor_comp (fiber_inclusion p b) F) :=
  @mapped_injective_resolution R C (fiber_category p b)
    (precomposition (module_category R) (fiber_inclusion p b))
    (@module_restriction_preserves_zero R (fiber_category p b) C (fiber_inclusion p b))
    (@module_restriction_preserves_exact R (fiber_category p b) C (fiber_inclusion p b))
    (@module_restriction_preserves_injections R (fiber_category p b) C (fiber_inclusion p b))
    (fun M => @fiber_restriction_preserves_injectives R C D p hp b M) F J.

Definition fiber_ran_resolution_complex : @diagram_complex R D :=
  mapped_diagram_complex (@module_ran_preserves_zero R C D p) (injective_resolution_complex J).

Definition fiber_ran_term_iso (b : D) n : @isomorphism (module_category R)
    (cochain_term (diagram_evaluation_complex fiber_ran_resolution_complex b) n)
    (cochain_term (limit_complex (injective_resolution_complex (fiber_restricted_resolution b))) n) :=
  module_ran_fiber_iso R hp b (diagram_term (injective_resolution_complex J) n).

Lemma fiber_ran_term_commutes (b : D) n v :
    cochain_d (limit_complex (injective_resolution_complex (fiber_restricted_resolution b))) n
      (module_hom_fun (iso_hom (fiber_ran_term_iso b n)) v) =
    module_hom_fun (iso_hom (fiber_ran_term_iso b n.+1))
      (cochain_d (diagram_evaluation_complex fiber_ran_resolution_complex b) n v).
Proof.
symmetry. exact (congr1 (fun h : module_hom
  (fobj (diagram_term fiber_ran_resolution_complex n) b)
  (module_limit_type (diagram_term (injective_resolution_complex (fiber_restricted_resolution b)) n.+1)) => h v)
  (naturality (iso_hom (@module_ran_fiber_nat_iso R C D p hp b))
    (diagram_d (injective_resolution_complex J) n))).
Qed.

Definition fiber_ran_cohomology_iso (b : D) n : @isomorphism (module_category R)
    [the lmodType R of cohomology (diagram_evaluation_complex fiber_ran_resolution_complex b) n]
    (resolution_cohomology (fiber_restricted_resolution b) n) :=
  term_iso_cohomology_iso (@fiber_ran_term_commutes b) n.

Hypothesis fibers_zero : forall b n
  (v : derived_limit R (functor_comp (fiber_inclusion p b) F) n), v = 0.

Lemma fiber_restricted_cohomology_zero b n
    (v : resolution_cohomology (fiber_restricted_resolution b) n) : v = 0.
Proof.
pose (e := derived_limit_resolution_iso (fiber_restricted_resolution b) n).
transitivity (module_hom_fun (iso_hom e) (module_hom_fun (iso_inv e) v)).
- symmetry; exact: module_iso_inv_hom_apply.
- have hz := @fibers_zero b n (module_hom_fun (iso_inv e) v).
  rewrite hz. exact: module_hom_zero.
Qed.

Lemma fiber_ran_cohomology_zero b n
    (v : cohomology (diagram_evaluation_complex fiber_ran_resolution_complex b) n) : v = 0.
Proof.
apply (@module_iso_hom_injective R _ _ (fiber_ran_cohomology_iso b n)).
rewrite module_hom_zero. exact: fiber_restricted_cohomology_zero.
Qed.

Lemma fiber_ran_resolution_exact : diagram_all_exact fiber_ran_resolution_complex.
Proof.
split.
- intros b v hv.
  exact (proj1 (cohomology_zero_iff (diagram_evaluation_complex fiber_ran_resolution_complex b) 0%N)
    (@fiber_ran_cohomology_zero b 0%N) v hv).
- intros n b v hv.
  exact (proj1 (cohomology_zero_iff (diagram_evaluation_complex fiber_ran_resolution_complex b) n.+1)
    (@fiber_ran_cohomology_zero b n.+1) v hv).
Qed.

Lemma fiber_ran_resolution_injective n :
    injective_object (functor_category D (module_category R))
      (diagram_term fiber_ran_resolution_complex n).
Proof.
apply module_ran_preserves_injectives. exact: injective_resolution_term_injective.
Qed.

Theorem fiber_vanishing_resolution_cohomology n
    (v : resolution_cohomology J n) : v = 0.
Proof.
pose (e := @mapped_limit_cohomology_iso R C D (module_ran R p)
  (@module_ran_preserves_zero R C D p) (module_ran_limit_nat_iso R p)
  (injective_resolution_complex J) n).
transitivity (module_hom_fun (iso_hom e) (module_hom_fun (iso_inv e) v)).
- symmetry; exact: module_iso_inv_hom_apply.
- have hz : module_hom_fun (iso_inv e) v = 0.
    exact (@exact_injective_limit_cohomology_zero R D fiber_ran_resolution_complex
      fiber_ran_resolution_exact fiber_ran_resolution_injective n (module_hom_fun (iso_inv e) v)).
  rewrite hz. exact: module_hom_zero.
Qed.
End FiberVanishing.

Theorem fiberwise_derived_limit_zero (R : pzRingType) {C D : category} (p : functor C D)
    (hp : fibration p) (F : module_diagram R C)
    (fibers_zero : forall b n (v : derived_limit R (functor_comp (fiber_inclusion p b) F) n), v = 0) :
    forall n (v : derived_limit R F n), v = 0.
Proof.
intros n v. exact (@fiber_vanishing_resolution_cohomology R C D p hp F
  (chosen_injective_resolution R F) fibers_zero n v).
Qed.
