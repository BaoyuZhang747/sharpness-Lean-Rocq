(** Higher limits defined by actual chosen injective resolutions. The
    identity and composition laws follow from comparison-map homotopy,
    not from a postulated derived-functor interface. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleLimits CategoryModuleLinear CategoryEnoughInjectives
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison
  CategoryResolutionLimitMaps HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalDiagramInjectives HomologicalDiagramLimits
  MackeyModuleCarriers MackeyModuleQuotient ModuleInfrastructure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.

Section MapLaws.
Variable R : pzRingType.
Variable C : category.

Definition diagram_cochain_identity (K : @diagram_complex R C) : diagram_cochain_map K K.
Proof.
refine (@Build_diagram_cochain_map R C K K (fun n => nat_id (diagram_term K n)) _).
intros n x v; reflexivity.
Defined.

Definition diagram_cochain_composition {K L M : @diagram_complex R C}
    (f : diagram_cochain_map K L) (g : diagram_cochain_map L M) : diagram_cochain_map K M.
Proof.
refine (@Build_diagram_cochain_map R C K M
  (fun n => nat_comp (diagram_cochain_map_at f n) (diagram_cochain_map_at g n)) _).
intros n x v.
change (module_hom_fun (component (diagram_d M n) x)
  (module_hom_fun (component (diagram_cochain_map_at g n) x)
    (module_hom_fun (component (diagram_cochain_map_at f n) x) v)) =
  module_hom_fun (component (diagram_cochain_map_at g n.+1) x)
    (module_hom_fun (component (diagram_cochain_map_at f n.+1) x)
      (module_hom_fun (component (diagram_d K n) x) v))).
rewrite !diagram_cochain_map_commutes. reflexivity.
Defined.

Definition injective_resolution_identity {F : module_diagram R C} (X : injective_resolution F) :
    injective_resolution_map X X (nat_id F).
Proof.
refine (@Build_injective_resolution_map R C F F X X (nat_id F)
  (diagram_cochain_identity (injective_resolution_complex X)) _).
apply nat_trans_ext; intro x; apply module_hom_ext; intro v; reflexivity.
Defined.

Definition injective_resolution_composition {F G H : module_diagram R C}
    {X : injective_resolution F} {Y : injective_resolution G} {Z : injective_resolution H}
    {u : nat_trans F G} {v : nat_trans G H}
    (a : injective_resolution_map X Y u) (b : injective_resolution_map Y Z v) :
    injective_resolution_map X Z (nat_comp u v).
Proof.
refine (@Build_injective_resolution_map R C F H X Z (nat_comp u v)
  (diagram_cochain_composition (resolution_map_complex a) (resolution_map_complex b)) _).
apply nat_trans_ext; intro x; apply module_hom_ext; intro w.
have ha := congr1 (fun t : nat_trans F (diagram_term (injective_resolution_complex Y) 0) =>
  module_hom_fun (component t x) w) (resolution_map_augmentation a).
have hb := congr1 (fun t : nat_trans G (diagram_term (injective_resolution_complex Z) 0) =>
  module_hom_fun (component t x) (module_hom_fun (component u x) w)) (resolution_map_augmentation b).
change (module_hom_fun (component (diagram_cochain_map_at (resolution_map_complex b) 0) x)
  (module_hom_fun (component (diagram_cochain_map_at (resolution_map_complex a) 0) x)
    (module_hom_fun (component (injective_resolution_augmentation X) x) w)) =
  module_hom_fun (component (injective_resolution_augmentation Z) x)
    (module_hom_fun (component v x) (module_hom_fun (component u x) w))).
change (module_hom_fun (component (diagram_cochain_map_at (resolution_map_complex a) 0) x) (module_hom_fun (component (injective_resolution_augmentation X) x) w) = module_hom_fun (component (injective_resolution_augmentation Y) x) (module_hom_fun (component u x) w)) in ha.
rewrite ha. exact hb.
Defined.

Lemma limit_cohomology_identity (K : @diagram_complex R C) n
    (q : cohomology (limit_complex K) n) :
    cohomology_map (limit_cochain_map (diagram_cochain_identity K)) n q = q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; apply module_limit_val_injective.
apply functional_extensionality_dep; intro x.
change (module_limit_val (limit_action (nat_id (diagram_term K n))
  (cycle_inclusion (limit_complex K) n z)) x =
  module_limit_val (cycle_inclusion (limit_complex K) n z) x).
rewrite limit_action_coordinate. reflexivity.
Qed.

Lemma limit_cohomology_composition {K L M : @diagram_complex R C}
    (f : diagram_cochain_map K L) (g : diagram_cochain_map L M) n
    (q : cohomology (limit_complex K) n) :
    cohomology_map (limit_cochain_map (diagram_cochain_composition f g)) n q =
      cohomology_map (limit_cochain_map g) n (cohomology_map (limit_cochain_map f) n q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; apply module_limit_val_injective.
apply functional_extensionality_dep; intro x.
change (module_limit_val (limit_action
  (nat_comp (diagram_cochain_map_at f n) (diagram_cochain_map_at g n))
  (cycle_inclusion (limit_complex K) n z)) x =
  module_limit_val (limit_action (diagram_cochain_map_at g n)
    (limit_action (diagram_cochain_map_at f n) (cycle_inclusion (limit_complex K) n z))) x).
rewrite !limit_action_coordinate. reflexivity.
Qed.
End MapLaws.

Local Opaque chosen_injective_resolution injective_resolution_comparison module_quotient linear_preimage linear_kernel linear_image.
Section DerivedLimits.
Variable R : pzRingType.
Variable C : category.

Definition derived_limit (F : module_diagram R C) n : lmodType R :=
  [the lmodType R of cohomology
    (limit_complex (injective_resolution_complex (chosen_injective_resolution R F))) n].

Definition derived_limit_map {F G : module_diagram R C} (u : nat_trans F G) n :
    module_hom (derived_limit F n) (derived_limit G n) :=
  module_hom_of_linear (cohomology_map
    (limit_cochain_map (resolution_map_complex
      (injective_resolution_comparison (chosen_injective_resolution R F)
        (chosen_injective_resolution R G) u))) n).

Lemma derived_limit_map_identity (F : module_diagram R C) n :
    derived_limit_map (nat_id F) n = module_hom_id (derived_limit F n).
Proof.
apply module_hom_ext; intro q.
change (cohomology_map (limit_cochain_map (resolution_map_complex
  (injective_resolution_comparison (chosen_injective_resolution R F)
    (chosen_injective_resolution R F) (nat_id F)))) n q = q).
rewrite (injective_resolution_cohomology_map_independent
  (injective_resolution_comparison (chosen_injective_resolution R F)
    (chosen_injective_resolution R F) (nat_id F))
  (injective_resolution_identity (chosen_injective_resolution R F)) q).
exact: limit_cohomology_identity.
Qed.

Lemma derived_limit_map_composition {F G H : module_diagram R C}
    (u : nat_trans F G) (v : nat_trans G H) n :
    derived_limit_map (nat_comp u v) n =
      module_hom_comp (derived_limit_map u n) (derived_limit_map v n).
Proof.
apply module_hom_ext; intro q.
change (cohomology_map (limit_cochain_map (resolution_map_complex
  (injective_resolution_comparison (chosen_injective_resolution R F)
    (chosen_injective_resolution R H) (nat_comp u v)))) n q =
  cohomology_map (limit_cochain_map (resolution_map_complex
    (injective_resolution_comparison (chosen_injective_resolution R G)
      (chosen_injective_resolution R H) v))) n
  (cohomology_map (limit_cochain_map (resolution_map_complex
    (injective_resolution_comparison (chosen_injective_resolution R F)
      (chosen_injective_resolution R G) u))) n q)).
transitivity (cohomology_map (limit_cochain_map (resolution_map_complex
  (injective_resolution_composition
    (injective_resolution_comparison (chosen_injective_resolution R F)
      (chosen_injective_resolution R G) u)
    (injective_resolution_comparison (chosen_injective_resolution R G)
      (chosen_injective_resolution R H) v)))) n q).
- exact: injective_resolution_cohomology_map_independent.
- exact: limit_cohomology_composition.
Qed.

Definition derived_limit_functor (n : nat) :
    functor (functor_category C (module_category R)) (module_category R).
Proof.
refine (@Build_functor (functor_category C (module_category R)) (module_category R)
  (fun F => derived_limit F n) (fun F G u => derived_limit_map u n) _ _).
- intro F; exact: derived_limit_map_identity.
- intros F G H u v; exact: derived_limit_map_composition.
Defined.
End DerivedLimits.

Arguments derived_limit R {C} F n.
Arguments derived_limit_map R {C F G} u n.
Arguments derived_limit_functor R C n.





