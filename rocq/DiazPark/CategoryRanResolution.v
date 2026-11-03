(** The actual right Kan functor transports injective resolutions whenever
    its comma limits have the proved discrete-initial-family exactness. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleProducts CategoryModuleLimits CategoryComma CategoryStructured CategoryInitialFamily
  CategoryModuleRightKan CategoryModuleInitialExact ModuleDiagrams
  HomologicalDiagramLimits CategoryInjectiveResolution CategoryResolutionTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section RanResolution.
Variable R : pzRingType.
Variables C D : category.
Variable L : functor C D.

Lemma module_ran_map_coordinate {F G : module_diagram R C} (a : nat_trans F G)
    d (v : fobj (fobj (module_ran R L) F) d) (X : structured_category L d) :
    module_limit_val (module_hom_fun (component (fmap (module_ran R L) a) d) v) X =
      module_hom_fun (component a (structured_source X)) (module_limit_val v X).
Proof.
exact (@limit_action_coordinate R (structured_category L d)
  (functor_comp (structured_projection L d) F)
  (functor_comp (structured_projection L d) G)
  (nat_whisker_left (structured_projection L d) a) v X).
Qed.

Theorem module_ran_preserves_zero : diagram_functor_preserves_zero (module_ran R L).
Proof.
intros F G d v. apply module_limit_val_injective.
apply functional_extensionality_dep; intro X.
rewrite module_ran_map_coordinate. reflexivity.
Qed.

Theorem module_ran_preserves_injections : diagram_functor_preserves_injections (module_ran R L).
Proof.
intros F G a ha d v w h. apply module_limit_val_injective.
apply functional_extensionality_dep; intro X.
apply (ha (structured_source X)).
have hx := congr1 (fun y => module_limit_val y X) h.
rewrite !module_ran_map_coordinate in hx. exact hx.
Qed.

Variable T : forall d, initial_family (structured_category L d).

Theorem module_ran_preserves_exact_from_family : diagram_functor_preserves_exact (module_ran R L).
Proof.
intros F G H a b he d v.
exact (@module_ran_initial_family_exact R C D L T F G H a b he d v).
Qed.

Definition ran_injective_resolution {F : module_diagram R C} (J : injective_resolution F) :
    injective_resolution (fobj (module_ran R L) F) :=
  @mapped_injective_resolution R C D (module_ran R L)
    module_ran_preserves_zero module_ran_preserves_exact_from_family
    module_ran_preserves_injections (fun F => @module_ran_preserves_injectives R C D L F) F J.
End RanResolution.

Arguments ran_injective_resolution R {C D} L T {F} J.


