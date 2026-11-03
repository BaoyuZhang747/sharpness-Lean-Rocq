(** Restriction to a full collection is an actual limit isomorphism when
    the deletion kernel has vanishing H0 and H1. Its components are literal
    restriction, not an unspecified isomorphism obtained from dimensions. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleExactness CategoryModuleProducts CategoryModuleLimits
  CategoryAtomicDeletionCore CategoryAtomicDeletionAdjunction
  CategoryAtomicDeletionSequence CategoryAtomicDeletionLimits
  ModuleInfrastructure MackeyModuleCarriers HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalModuleIso HomologicalShortExactMaps
  BarComplex BarNaturality BarDegreeZero BarDerivedComparison HomologicalDiagramLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DiazParkBarComplex DiazParkBarNaturality
  DiazParkBarDegreeZero DiazParkBarDerivedComparison.
Local Open Scope ring_scope.

Module DPCollectionLimitRestriction.
Section Restriction.
Variable R : pzRingType.
Variable C : category.
Variable P : C -> Prop.
Variable Pup : forall (x y : C), hom C x y -> P x -> P y.
Variable D : module_codiagram R C.
Local Notation E := (fobj (full_restriction R P) D).
Hypothesis h0 : forall q : cohomology (bar_complex (deletion_kernel Pup D)) 0, q = 0.
Hypothesis h1 : forall q : cohomology (bar_complex (deletion_kernel Pup D)) 1, q = 0.

Definition collection_limit_iso : @isomorphism (module_category R)
    (module_limit_type D) (module_limit_type E) :=
  module_iso_comp (iso_symm (bar_zero_cohomology_limit_iso D))
    (module_iso_comp (cohomology_quotient_iso (deletion_bar_short_exact Pup D) h0 h1)
      (module_iso_comp (bar_zero_cohomology_limit_iso (deletion_truncation Pup D))
        (zero_extension_limit_iso Pup E))).

Theorem collection_limit_iso_component (v : module_limit_type D)
    (x : C) (hx : P x) :
  module_limit_val (module_hom_fun (iso_hom collection_limit_iso) v) (exist _ x hx) =
    module_limit_val v x.
Proof.
change (module_limit_val
  (module_hom_fun (iso_hom (bar_zero_cohomology_limit_iso (deletion_truncation Pup D)))
    (cohomology_map (bar_cochain_map (zero_extension_unit Pup D)) 0
      (module_hom_fun (iso_inv (bar_zero_cohomology_limit_iso D)) v))) x hx =
  module_limit_val v x).
rewrite -bar_zero_limit_naturality module_iso_inv_hom_apply limit_action_coordinate.
reflexivity.
Qed.

Definition literal_limit_restriction : module_hom (module_limit_type D) (module_limit_type E).
Proof.
exists (fun v : module_limit_type D => @submodule_in R (module_product_type (fobj E)) (module_limit_subspace E)
  (fun x => module_limit_val v (proj1_sig x))
  (fun x y f => module_limit_val_compatible v f)).
move=> r v w; apply module_limit_val_injective; reflexivity.
Defined.

Theorem collection_limit_iso_hom :
  iso_hom collection_limit_iso = literal_limit_restriction.
Proof.
apply module_hom_ext => v; apply module_limit_val_injective.
apply functional_extensionality_dep => x; case: x => x hx.
exact: collection_limit_iso_component.
Qed.

End Restriction.
End DPCollectionLimitRestriction.
