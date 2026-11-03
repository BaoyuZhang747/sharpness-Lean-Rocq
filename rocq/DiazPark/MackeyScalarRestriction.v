(** General scalar restriction for full Mackey modules, using the exact
    scalar functor of the proved native higher-limit comparison. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryModules CategoryDerivedLimits
  CategoryAtomicDeletionTheorem MackeyStructures MackeyBarReduction
  HomologicalScalarRestriction BarScalarHigherLimits BarHigherLimitVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkScalarRestriction DiazParkScalarHigherLimits
  DiazParkBarHigherLimitVanishing.
Local Open Scope ring_scope.

Module DPMackeyScalarRestriction.
Section Restriction.
Variables A B : comPzRingType.
Variable phi : {rmorphism A -> B}.
Variable C : category.
Variable shape : mackey_shape C.
Variable M : mackey_module B shape.

Definition restricted_mackey : mackey_module A shape :=
  @MackeyModule A C shape
    (fun P => restricted_module_type phi (mackey_value M P))
    (fun P Q f => restricted_linear phi (mackey_pull M f))
    (fun P Q f => restricted_linear phi (mackey_push M f))
    (@mackey_pull_id _ _ _ M) (@mackey_push_id _ _ _ M)
    (@mackey_pull_comp _ _ _ M) (@mackey_push_comp _ _ _ M)
    (@mackey_pull_iso _ _ _ M) (@mackey_formula _ _ _ M).

Variable D : category.
Variable L : functor D C.

Lemma restricted_mackey_codiagram :
  mackey_codiagram L restricted_mackey = restriction_diagram phi (mackey_codiagram L M).
Proof.
apply: (@functor_extensionality (opposite D) (module_category A)
  (mackey_codiagram L restricted_mackey)
  (restriction_diagram phi (mackey_codiagram L M)) (Logic.eq_refl _)).
apply functional_extensionality_dep => P.
apply functional_extensionality_dep => Q.
apply functional_extensionality_dep => f.
apply module_hom_ext => x; reflexivity.
Qed.

Definition restricted_mackey_higher_limit_iso n : @isomorphism (module_category A)
    (restricted_module_type phi (derived_limit B (mackey_codiagram L M) n))
    (derived_limit A (mackey_codiagram L restricted_mackey) n).
Proof.
rewrite restricted_mackey_codiagram; exact: scalar_higher_limit_iso.
Defined.

Theorem restricted_mackey_higher_limit_zero_iff n :
  (forall q : derived_limit B (mackey_codiagram L M) n, q = 0) <->
  (forall q : derived_limit A (mackey_codiagram L restricted_mackey) n, q = 0).
Proof. exact: module_iso_zero_iff (restricted_mackey_higher_limit_iso n). Qed.

Theorem restricted_mackey_bar_acyclic_iff :
  mackey_bar_acyclic L M <-> mackey_bar_acyclic L restricted_mackey.
Proof.
rewrite /mackey_bar_acyclic !bar_derived_positive_zero_iff.
split=> h n.
- apply/(restricted_mackey_higher_limit_zero_iff n.+1); exact: h.
- apply/(restricted_mackey_higher_limit_zero_iff n.+1); exact: h.
Qed.

End Restriction.
End DPMackeyScalarRestriction.
