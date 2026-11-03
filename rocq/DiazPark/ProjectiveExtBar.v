(** The constructed bar is an actual projective resolution of constant R,
    and Hom from it is the literal category-bar cochain complex. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  CategoryDiagramHom CategoryDiagramHomLimit CategoryEnoughProjectives
  CategoryEnoughProjectivesResolution ProjectiveExtComplex CategoryComplexIso
  BarComplex BarResolutionTerms BarResolutionHom BarResolutionProjective
  BarResolutionDifferential BarResolutionAugmentation BarResolutionContraction
  BarResolutionComparison HomologicalComplex HomologicalCohomology
  HomologicalModuleIso MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectives DPEnoughProjectiveResolutions DPProjectiveExt
  DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DiazParkBarComplex DiazParkBarResolutionTerms DiazParkBarResolutionHom
  DiazParkBarResolutionProjective DiazParkBarResolutionDifferential
  DiazParkBarResolutionAugmentation DiazParkBarResolutionContraction DiazParkBarResolutionComparison.
Local Open Scope ring_scope.
Local Opaque module_quotient.

Module DPProjectiveExtBar.
Section BarResolution.
Variables (R : comPzRingType) (C : category).

Lemma bar_term_projective n : projective_object
    (functor_category (opposite C) (module_category R)) (@resolution_term R C n).
Proof.
intros D E q hq f.
exact (@resolution_term_lift R C D E q (@epi_pointwise_surjective R (opposite C) D E q hq) n f).
Qed.

Definition bar_projective_resolution : projective_resolution (constant_regular_diagram R (opposite C)).
Proof.
refine (@Build_projective_resolution R (opposite C) (constant_regular_diagram R (opposite C))
  (@resolution_term R C) (@resolution_boundary R C) (@resolution_augmentation R C)
  bar_term_projective (@resolution_augmentation_surjective R C)
  (@resolution_boundary_squared R C) (@resolution_augmentation_boundary R C) _ _).
- intros x v; split; first exact: resolution_exact_zero.
  intros [u <-]; exact: resolution_augmentation_boundary.
- intros n x v; split; first exact: resolution_exact_successor.
  intros [u <-]; exact: resolution_boundary_squared.
Defined.

Variable D : module_codiagram R C.
Definition bar_hom_to_cochain n (f : diagram_hom_type (@resolution_term R C n) D) :
    bar_term D n := term_to_cochain f.
Lemma bar_hom_to_cochain_linear n : linear (@bar_hom_to_cochain n).
Proof.
intros a f g; apply functional_extensionality_dep; intro x.
apply functional_extensionality_dep; intro p; reflexivity.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R
  (diagram_hom_type (@resolution_term R C n) D) (bar_term D n) _
  (@bar_hom_to_cochain n) (@bar_hom_to_cochain_linear n).

Definition bar_hom_term_iso n : @isomorphism (module_category R)
    (cochain_term (projective_hom_complex bar_projective_resolution D) n)
    (cochain_term (bar_complex D) n).
Proof.
apply (@linear_bijection_iso R _ _ (@bar_hom_to_cochain n : {linear _ -> _})).
- exact: term_to_cochain_injective.
- intro a; exists (cochain_to_term a); exact: term_cochain_inverse.
Defined.

Lemma bar_hom_term_commutes n f :
    cochain_d (bar_complex D) n (module_hom_fun (iso_hom (bar_hom_term_iso n)) f) =
    module_hom_fun (iso_hom (bar_hom_term_iso n.+1))
      (cochain_d (projective_hom_complex bar_projective_resolution D) n f).
Proof. symmetry; exact: term_cochain_differential. Qed.

Definition bar_projective_cohomology_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology (projective_hom_complex bar_projective_resolution D) n]
    [the lmodType R of cohomology (bar_complex D) n] :=
  term_iso_cohomology_iso bar_hom_term_commutes n.
End BarResolution.
End DPProjectiveExtBar.
