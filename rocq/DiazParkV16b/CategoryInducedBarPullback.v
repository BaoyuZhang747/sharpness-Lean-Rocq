(** The actual induced-to-ordinary bar comparison lifts identity on constant
    coefficients. Its Hom map is precisely the literal category pullback. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  CategoryDiagramHomLimit CategoryEnoughProjectivesResolution CategoryEnoughProjectivesComparison
  BarPaths BarFreeModule BarComplex BarNaturality BarResolutionTerms BarResolutionHom
  BarResolutionDifferential BarResolutionAugmentation BarResolutionComparison ProjectiveExtBar.
From DiazParkV16b Require Import CategoryBarPullback CategoryInducedBarTerms
  CategoryInducedBarHom CategoryInducedBarDifferential CategoryInducedBarAugmentation
  CategoryInducedBarResolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule DiazParkBarComplex
  DiazParkBarNaturality DiazParkBarResolutionTerms DiazParkBarResolutionHom
  DiazParkBarResolutionDifferential DiazParkBarResolutionAugmentation
  DiazParkBarResolutionComparison DPEnoughProjectiveResolutions DPProjectiveComparison
  DPProjectiveExtBar DPCategoryBarPullbackMaps.
Local Open Scope ring_scope.

Section ComparisonTerms.
Variable R : pzRingType.
Variables C D : category.
Variable q : functor C D.

Definition induced_bar_comparison_term n :
    nat_trans (induced_bar_term R q n) (@resolution_term R D n) :=
  induced_bar_from_cochain q
    (bar_pullback_at q (@resolution_term R D n) n
      (@term_to_cochain R D (@resolution_term R D n) n (nat_id (@resolution_term R D n)))).

Lemma induced_bar_comparison_hom n {M : module_codiagram R D}
    (a : nat_trans (@resolution_term R D n) M) :
    induced_bar_to_cochain q (nat_comp (induced_bar_comparison_term n) a) =
    bar_pullback_at q M n (term_to_cochain a).
Proof.
rewrite induced_bar_postcompose /induced_bar_comparison_term induced_bar_cochain_inverse.
rewrite -bar_pullback_coefficient_naturality.
reflexivity.
Qed.

Theorem induced_bar_comparison_boundary n :
    nat_comp (induced_bar_comparison_term n.+1) (@resolution_boundary R D n) =
    nat_comp (induced_bar_boundary R q n) (induced_bar_comparison_term n).
Proof.
apply (@induced_bar_to_cochain_injective R C D q (@resolution_term R D n) n.+1).
rewrite induced_bar_comparison_hom induced_bar_to_cochain_boundary
  /induced_bar_comparison_term induced_bar_cochain_inverse bar_pullback_d.
apply f_equal.
exact (@term_cochain_differential R D (@resolution_term R D n) n
  (nat_id (@resolution_term R D n))).
Qed.
End ComparisonTerms.

Arguments induced_bar_comparison_term R {C D} q n.

Section Augmentation.
Variable R : comPzRingType.
Variables C D : category.
Variable q : functor C D.

Lemma induced_bar_comparison_augmentation :
    nat_comp (induced_bar_comparison_term R q 0%N) (@resolution_augmentation R D) =
    induced_bar_augmentation R q.
Proof.
apply (@induced_bar_to_cochain_injective R C D q
  (constant_regular_diagram R (opposite D)) 0%N).
rewrite induced_bar_comparison_hom /induced_bar_augmentation induced_bar_cochain_inverse.
apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intro s.
change (@resolution_augmentation_fun R D (fobj q c)
  (free_basis R (existT _ (fobj q c) (identity (fobj q c), tt))) = 1).
exact: resolution_augmentation_basis.
Qed.

Hypothesis augmentation_surjective : forall d (a : R^o),
  exists v, module_hom_fun (component (induced_bar_augmentation R q) d) v = a.
Hypothesis augmentation_exact : forall d (v : fobj (induced_bar_term R q 0%N) d),
  module_hom_fun (component (induced_bar_augmentation R q) d) v = 0 ->
  exists w, module_hom_fun (component (induced_bar_boundary R q 0%N) d) w = v.
Hypothesis successor_exact : forall n d (v : fobj (induced_bar_term R q n.+1) d),
  module_hom_fun (component (induced_bar_boundary R q n) d) v = 0 ->
  exists w, module_hom_fun (component (induced_bar_boundary R q n.+1) d) w = v.

Definition induced_bar_comparison_resolution : projective_resolution_map
    (@induced_bar_projective_resolution R C D q augmentation_surjective augmentation_exact successor_exact)
    (@bar_projective_resolution R D) (nat_id (constant_regular_diagram R (opposite D))).
Proof.
refine (@Build_projective_resolution_map R (opposite D)
  (constant_regular_diagram R (opposite D)) (constant_regular_diagram R (opposite D))
  (@induced_bar_projective_resolution R C D q augmentation_surjective augmentation_exact successor_exact)
  (@bar_projective_resolution R D) (nat_id (constant_regular_diagram R (opposite D)))
  (induced_bar_comparison_term R q) _ _).
- intros n d v.
  exact (congr1 (fun a : nat_trans (induced_bar_term R q n.+1) (@resolution_term R D n) =>
    module_hom_fun (component a d) v) (@induced_bar_comparison_boundary R C D q n)).
- apply nat_trans_ext; intro d; apply module_hom_ext; intro v.
  exact (congr1 (fun a : nat_trans (induced_bar_term R q 0%N)
    (constant_regular_diagram R (opposite D)) => module_hom_fun (component a d) v)
    induced_bar_comparison_augmentation).
Defined.
End Augmentation.
