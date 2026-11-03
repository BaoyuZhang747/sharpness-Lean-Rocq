(** Any two actual injective resolutions compute canonically isomorphic
    higher-limit modules. The comparison isomorphism is proved by the
    constructed comparison maps and their homotopies. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleLinear CategoryModuleLimits ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps HomologicalDiagramLimits
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison
  CategoryResolutionLimitMaps CategoryDerivedLimits CategoryEnoughInjectives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.
Local Opaque module_quotient linear_preimage linear_kernel linear_image
  chosen_injective_resolution injective_resolution_comparison.

Section Independence.
Variable R : pzRingType.
Variable C : category.

Definition injective_resolution_map_rebase {F G : module_diagram R C}
    {X : injective_resolution F} {Y : injective_resolution G}
    {u v : nat_trans F G} (h : u = v) (a : injective_resolution_map X Y u) :
    injective_resolution_map X Y v.
Proof.
refine (@Build_injective_resolution_map R C F G X Y v (resolution_map_complex a) _).
rewrite -h; exact: resolution_map_augmentation.
Defined.

Definition resolution_cohomology {F : module_diagram R C} (X : injective_resolution F) n : lmodType R :=
  [the lmodType R of cohomology (limit_complex (injective_resolution_complex X)) n].

Definition resolution_cohomology_map {F G : module_diagram R C}
    {X : injective_resolution F} {Y : injective_resolution G} {u : nat_trans F G}
    (a : injective_resolution_map X Y u) n :
    module_hom (resolution_cohomology X n) (resolution_cohomology Y n) :=
  module_hom_of_linear (cohomology_map (limit_cochain_map (resolution_map_complex a)) n).

Lemma resolution_cohomology_map_independent {F G : module_diagram R C}
    {X : injective_resolution F} {Y : injective_resolution G} {u : nat_trans F G}
    (a b : injective_resolution_map X Y u) n :
    resolution_cohomology_map a n = resolution_cohomology_map b n.
Proof. apply module_hom_ext; intro q; exact: injective_resolution_cohomology_map_independent. Qed.

Lemma resolution_cohomology_map_composition {F G H : module_diagram R C}
    {X : injective_resolution F} {Y : injective_resolution G} {Z : injective_resolution H}
    {u : nat_trans F G} {v : nat_trans G H}
    (a : injective_resolution_map X Y u) (b : injective_resolution_map Y Z v) n :
    resolution_cohomology_map (injective_resolution_composition a b) n =
      module_hom_comp (resolution_cohomology_map a n) (resolution_cohomology_map b n).
Proof. apply module_hom_ext; intro q; exact: limit_cohomology_composition. Qed.

Lemma resolution_cohomology_map_identity {F : module_diagram R C}
    (X : injective_resolution F) n :
    resolution_cohomology_map (injective_resolution_identity X) n = module_hom_id _.
Proof. apply module_hom_ext; intro q; exact: limit_cohomology_identity. Qed.

Lemma identity_lifts_inverse {F : module_diagram R C}
    {X Y : injective_resolution F}
    (a : injective_resolution_map X Y (nat_id F))
    (b : injective_resolution_map Y X (nat_id F)) n :
    module_hom_comp (resolution_cohomology_map a n) (resolution_cohomology_map b n) = module_hom_id _.
Proof.
pose (c := injective_resolution_map_rebase
  (@compose_id_left (functor_category C (module_category R)) F F (nat_id F))
  (injective_resolution_composition a b)).
transitivity (resolution_cohomology_map c n).
- symmetry; exact: resolution_cohomology_map_composition.
- transitivity (resolution_cohomology_map (injective_resolution_identity X) n).
  + exact: resolution_cohomology_map_independent.
  + exact: resolution_cohomology_map_identity.
Qed.

Definition resolution_cohomology_iso {F : module_diagram R C}
    (X Y : injective_resolution F) n :
    @isomorphism (module_category R) (resolution_cohomology X n) (resolution_cohomology Y n).
Proof.
refine (@Build_isomorphism (module_category R) (resolution_cohomology X n) (resolution_cohomology Y n)
  (resolution_cohomology_map (injective_resolution_comparison X Y (nat_id F)) n)
  (resolution_cohomology_map (injective_resolution_comparison Y X (nat_id F)) n) _ _).
- exact: identity_lifts_inverse.
- exact: identity_lifts_inverse.
Defined.

Theorem resolution_cohomology_iso_naturality {F G : module_diagram R C}
    {X X' : injective_resolution F} {Y Y' : injective_resolution G}
    {u : nat_trans F G} (a : injective_resolution_map X Y u)
    (b : injective_resolution_map X' Y' u) n :
    module_hom_comp (resolution_cohomology_map a n) (iso_hom (resolution_cohomology_iso Y Y' n)) =
      module_hom_comp (iso_hom (resolution_cohomology_iso X X' n)) (resolution_cohomology_map b n).
Proof.
pose (c := injective_resolution_map_rebase
  (@compose_id_right (functor_category C (module_category R)) F G u)
  (injective_resolution_composition a (injective_resolution_comparison Y Y' (nat_id G)))).
pose (d := injective_resolution_map_rebase
  (@compose_id_left (functor_category C (module_category R)) F G u)
  (injective_resolution_composition (injective_resolution_comparison X X' (nat_id F)) b)).
transitivity (resolution_cohomology_map c n).
- symmetry; exact: resolution_cohomology_map_composition.
- transitivity (resolution_cohomology_map d n).
  + exact: resolution_cohomology_map_independent.
  + exact: resolution_cohomology_map_composition.
Qed.

Definition derived_limit_resolution_iso {F : module_diagram R C}
    (X : injective_resolution F) n :
    @isomorphism (module_category R) (derived_limit R F n) (resolution_cohomology X n) :=
  resolution_cohomology_iso (chosen_injective_resolution R F) X n.
End Independence.

Arguments resolution_cohomology {R C F} X n.
Arguments resolution_cohomology_map {R C F G X Y u} a n.
Arguments resolution_cohomology_iso {R C F} X Y n.
Arguments derived_limit_resolution_iso {R C F} X n.
