(** Positive derived limits of arbitrary contravariant modules vanish on
    a category with a terminal object. This is proved on the actual resolution. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryLimits CategoryComma CategoryModules
  CategoryModuleLimits CategoryInjectiveResolution CategoryEnoughInjectives
  CategoryDerivedLimits HomologicalComplex HomologicalCohomology
  HomologicalDiagramInjectives HomologicalDiagramLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology.
Local Open Scope ring_scope.

Section TerminalLimit.
Variable R : pzRingType.
Variable C : category.
Variable t : terminal_object C.
Variable D : module_codiagram R C.

Lemma module_limit_terminal_injective :
    injective (fun v : module_limit_type D => module_limit_val v (terminal_point t)).
Proof.
  move=> u v he. apply module_limit_val_injective.
  apply functional_extensionality_dep => x.
  rewrite -(module_limit_val_compatible u (terminal_arrow t x))
    -(module_limit_val_compatible v (terminal_arrow t x)) he. reflexivity.
Qed.

Definition module_limit_terminal_extend (v : fobj D (terminal_point t)) : module_limit_type D :=
  module_hom_fun (module_limit_lift (initial_cone D (terminal_initial_op t))) v.
Lemma module_limit_terminal_extend_top (v : fobj D (terminal_point t)) :
    module_limit_val (module_limit_terminal_extend v) (terminal_point t) = v.
Proof.
  change (module_hom_fun (fmap D (terminal_arrow t (terminal_point t))) v = v).
  rewrite terminal_arrow_self fmap_id. reflexivity.
Qed.
End TerminalLimit.

Theorem terminal_injective_resolution_positive_zero (R : pzRingType)
    (C : category) (t : terminal_object C) (D : module_codiagram R C)
    (J : injective_resolution D) n :
    forall q : cohomology (limit_complex (injective_resolution_complex J)) n.+1, q = 0.
Proof.
  apply/cohomology_zero_iff => v hv.
  pose K := injective_resolution_complex J.
  change (limit_action (diagram_d K n.+1) v = 0) in hv.
  have ht : module_hom_fun (component (diagram_d K n.+1) (terminal_point t))
      (module_limit_val v (terminal_point t)) = 0.
    have h := congr1 (fun w : module_limit_type (diagram_term K n.+2) =>
      module_limit_val w (terminal_point t)) hv.
    change (module_limit_val (limit_action (diagram_d K n.+1) v) (terminal_point t) = 0) in h.
    by rewrite limit_action_coordinate in h.
  have [w hw] := injective_resolution_exact_successor J n (terminal_point t)
    (module_limit_val v (terminal_point t)) ht.
  exists (@module_limit_terminal_extend R C t (diagram_term K n) w).
  apply (@module_limit_terminal_injective R C t (diagram_term K n.+1)).
  change (module_limit_val (limit_action (diagram_d K n)
    (@module_limit_terminal_extend R C t (diagram_term K n) w)) (terminal_point t) = module_limit_val v (terminal_point t)).
  by rewrite limit_action_coordinate module_limit_terminal_extend_top.
Qed.

Theorem terminal_derived_limits_positive_zero (R : pzRingType)
    (C : category) (t : terminal_object C) (D : module_codiagram R C) n :
    forall q : derived_limit R D n.+1, q = 0.
Proof. exact (@terminal_injective_resolution_positive_zero R C t D
  (chosen_injective_resolution R D) n). Qed.

Theorem slice_derived_limits_positive_zero (R : pzRingType)
    (C : category) (P : C) (D : module_codiagram R (over_category C P)) n :
    forall q : derived_limit R D n.+1, q = 0.
Proof. exact (@terminal_derived_limits_positive_zero R (over_category C P) (@over_terminal C P) D n). Qed.
