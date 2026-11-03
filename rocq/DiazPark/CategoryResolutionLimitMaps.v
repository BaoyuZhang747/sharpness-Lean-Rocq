(** Applying the actual module limit functor to diagram cochain maps and
    natural homotopies. Comparison lifts therefore induce the same map on
    the actual quotient cohomology modules in every degree. *)
From mathcomp Require Import all_ssreflect ssralg boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleProducts
  CategoryModuleLimits HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalDiagramInjectives HomologicalDiagramLimits
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison
  CategoryInjectiveResolutionHomotopy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.

Lemma module_limit_val_sub {R : pzRingType} {C : category}
    (F : module_diagram R C) (v w : module_limit_type F) :
    module_limit_val (v - w) = module_limit_val v - module_limit_val w.
Proof. exact ((GRing.zmod_morphism_linear (@module_limit_val_linear R C F)) v w). Qed.

Lemma module_limit_val_add {R : pzRingType} {C : category}
    (F : module_diagram R C) (v w : module_limit_type F) :
    module_limit_val (v + w) = module_limit_val v + module_limit_val w.
Proof.
  have h := @module_limit_val_linear R C F 1 v w.
  by rewrite !scale1r in h.
Qed.

Section LimitMaps.
Variable R : pzRingType.
Variable C : category.
Variables K L : @diagram_complex R C.

Definition limit_cochain_map (f : diagram_cochain_map K L) :
    cochain_map (limit_complex K) (limit_complex L).
Proof.
  refine (@CochainMap R (limit_complex K) (limit_complex L)
    (fun n => (limit_action (diagram_cochain_map_at f n) :
      {linear module_limit_type (diagram_term K n) ->
        module_limit_type (diagram_term L n)})) _).
  intros n v. apply module_limit_val_injective.
  apply functional_extensionality_dep. intro x.
  change (module_limit_val (limit_action (diagram_d L n)
    (limit_action (diagram_cochain_map_at f n) v)) x =
    module_limit_val (limit_action (diagram_cochain_map_at f n.+1)
      (limit_action (diagram_d K n) v)) x).
  rewrite !limit_action_coordinate.
  exact (diagram_cochain_map_commutes f n x (module_limit_val v x)).
Defined.

Definition limit_cochain_homotopy (f g : diagram_cochain_map K L)
    (h : diagram_cochain_homotopy f g) :
    cochain_homotopy (limit_cochain_map f) (limit_cochain_map g).
Proof.
  refine (@CochainHomotopy R (limit_complex K) (limit_complex L)
    (limit_cochain_map f) (limit_cochain_map g)
    (fun n => (limit_action (diagram_homotopy_at h n) :
      {linear module_limit_type (diagram_term K n.+1) ->
        module_limit_type (diagram_term L n)})) _ _).
  - intro v. apply module_limit_val_injective.
    change (module_limit_val
      (limit_action (diagram_cochain_map_at f 0%N) v -
       limit_action (diagram_cochain_map_at g 0%N) v) =
      module_limit_val (limit_action (diagram_homotopy_at h 0%N)
        (limit_action (diagram_d K 0%N) v))).
    rewrite module_limit_val_sub. apply functional_extensionality_dep. intro x.
    change (module_limit_val (limit_action (diagram_cochain_map_at f 0%N) v) x -
      module_limit_val (limit_action (diagram_cochain_map_at g 0%N) v) x =
      module_limit_val (limit_action (diagram_homotopy_at h 0%N)
        (limit_action (diagram_d K 0%N) v)) x).
    rewrite !limit_action_coordinate. exact (diagram_homotopy_zero h x (module_limit_val v x)).
  - intros n v. apply module_limit_val_injective.
    change (module_limit_val
      (limit_action (diagram_cochain_map_at f n.+1) v -
       limit_action (diagram_cochain_map_at g n.+1) v) =
      module_limit_val
       (limit_action (diagram_d L n) (limit_action (diagram_homotopy_at h n) v) +
        limit_action (diagram_homotopy_at h n.+1) (limit_action (diagram_d K n.+1) v))).
    rewrite module_limit_val_sub module_limit_val_add.
    apply functional_extensionality_dep. intro x.
    change (module_limit_val (limit_action (diagram_cochain_map_at f n.+1) v) x -
      module_limit_val (limit_action (diagram_cochain_map_at g n.+1) v) x =
      module_limit_val (limit_action (diagram_d L n)
        (limit_action (diagram_homotopy_at h n) v)) x +
      module_limit_val (limit_action (diagram_homotopy_at h n.+1)
        (limit_action (diagram_d K n.+1) v)) x).
    rewrite !limit_action_coordinate. exact (diagram_homotopy_succ h n x (module_limit_val v x)).
Defined.
End LimitMaps.

Theorem injective_resolution_cohomology_map_independent
    {R : pzRingType} {C : category} {F G : module_diagram R C}
    {X : injective_resolution F} {Y : injective_resolution G} {u : nat_trans F G}
    (a b : injective_resolution_map X Y u) n
    (q : cohomology (limit_complex (injective_resolution_complex X)) n) :
    cohomology_map (limit_cochain_map (resolution_map_complex a)) n q =
      cohomology_map (limit_cochain_map (resolution_map_complex b)) n q.
Proof.
  exact (cohomology_map_homotopy
    (limit_cochain_homotopy (injective_resolution_maps_homotopic a b)) q).
Qed.


