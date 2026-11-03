(** Computation from the actual induced bar, assuming its explicit augmented
    exactness. These hypotheses are properties of the constructed maps; they
    remain to be discharged by the actual comma-chain contraction. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryDiagramHomLimit
  CategoryEnoughProjectivesResolution ProjectiveExtComplex ProjectiveExtComparison
  CategoryDiagramExtLimits CategoryDerivedLimits BarComplex BarDerivedComparison
  CategoryComplexIso HomologicalComplex HomologicalCohomology HomologicalModuleIso
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import CategoryInducedBarTerms CategoryInducedBarHom
  CategoryInducedBarProjective CategoryInducedBarDifferential CategoryInducedBarAugmentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectiveResolutions DPProjectiveExt
  DPProjectiveExtComparison DiazParkBarComplex DiazParkBarDerivedComparison
  DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Section Resolution.
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

Definition induced_bar_projective_resolution :
    projective_resolution (constant_regular_diagram R (opposite D)).
Proof.
refine (@Build_projective_resolution R (opposite D)
  (constant_regular_diagram R (opposite D))
  (induced_bar_term R q) (induced_bar_boundary R q) (induced_bar_augmentation R q)
  (@induced_bar_term_projective R C D q) augmentation_surjective
  (@induced_bar_boundary_squared_apply R C D q)
  (@induced_bar_augmentation_boundary_apply R C D q) _ _).
- intros d v; split; first exact: augmentation_exact.
  intros [w <-]; exact: induced_bar_augmentation_boundary_apply.
- intros n d v; split; first exact: successor_exact.
  intros [w <-]; exact: induced_bar_boundary_squared_apply.
Defined.

Variable M : module_codiagram R D.

Lemma induced_bar_hom_complex_commutes n a :
    cochain_d (bar_complex (functor_comp (functor_op q) M)) n
      (module_hom_fun (iso_hom (@induced_bar_hom_term_iso R C D q M n)) a) =
    module_hom_fun (iso_hom (@induced_bar_hom_term_iso R C D q M n.+1))
      (cochain_d (projective_hom_complex induced_bar_projective_resolution M) n a).
Proof. symmetry; exact: induced_bar_to_cochain_boundary. Qed.

Definition induced_bar_hom_cohomology_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology
      (projective_hom_complex induced_bar_projective_resolution M) n]
    [the lmodType R of cohomology (bar_complex (functor_comp (functor_op q) M)) n] :=
  @term_iso_cohomology_iso R
    (projective_hom_complex induced_bar_projective_resolution M)
    (bar_complex (functor_comp (functor_op q) M))
    (@induced_bar_hom_term_iso R C D q M) induced_bar_hom_complex_commutes n.

Definition induced_bar_higher_limit_iso n : @isomorphism (module_category R)
    (derived_limit R M n) (derived_limit R (functor_comp (functor_op q) M) n) :=
  module_iso_comp (iso_symm (constant_ext_derived_limit_iso M n))
    (module_iso_comp (iso_symm
      (@projective_resolution_ext_iso R D induced_bar_projective_resolution M n))
      (module_iso_comp (induced_bar_hom_cohomology_iso n)
        (bar_derived_limit_iso (functor_comp (functor_op q) M) n))).
End Resolution.
