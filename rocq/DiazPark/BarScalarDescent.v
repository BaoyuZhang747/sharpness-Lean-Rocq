(** Quotient-ring actions on actual Mackey coefficients and the genuine
    higher-limit comparison with their original scalar action. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryDerivedLimits CategoryAtomicDeletionTheorem
  MackeyStructures MackeyBarReduction HomologicalComplex HomologicalModuleIso
  HomologicalScalarRestriction ModuleScalarDescent BarScalarHigherLimits BarHigherLimitVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPScalarDescent DiazParkScalarRestriction DiazParkScalarHigherLimits
  DiazParkHomologicalModuleIso DiazParkBarHigherLimitVanishing.
Local Open Scope ring_scope.

Module DPBarScalarDescent.
Section Descent.
Variables A B : comPzRingType.
Variable phi : {rmorphism A -> B}.
Hypothesis onto : forall b, exists a, phi a = b.
Variable C : category.
Variable shape : mackey_shape C.
Variable M : mackey_module A shape.
Hypothesis annihilates : forall P a, phi a = 0 -> forall x : mackey_value M P, a *: x = 0.

Definition descended_mackey : mackey_module B shape :=
  @MackeyModule B C shape
    (fun P => @descended_module_type A B phi onto (mackey_value M P) (@annihilates P))
    (fun P Q f => @descended_linear A B phi onto _ _
      (@annihilates Q) (@annihilates P) (mackey_pull M f))
    (fun P Q f => @descended_linear A B phi onto _ _
      (@annihilates P) (@annihilates Q) (mackey_push M f))
    (@mackey_pull_id _ _ _ M) (@mackey_push_id _ _ _ M)
    (@mackey_pull_comp _ _ _ M) (@mackey_push_comp _ _ _ M)
    (@mackey_pull_iso _ _ _ M) (@mackey_formula _ _ _ M).

Variable D : category.
Variable L : functor D C.

Definition descended_coefficient_iso : @isomorphism
    (functor_category (opposite D) (module_category A))
    (mackey_codiagram L M)
    (restriction_diagram phi (mackey_codiagram L descended_mackey)).
Proof.
apply: (@nat_iso_of_components _ _ (mackey_codiagram L M)
  (restriction_diagram phi (mackey_codiagram L descended_mackey))
  (fun P => @descent_restriction_iso A B phi onto (mackey_value M (fobj L P))
    (@annihilates (fobj L P)))).
move=> P Q f; apply module_hom_ext => x; reflexivity.
Defined.

Definition descended_higher_limit_iso n : @isomorphism (module_category A)
    (derived_limit A (mackey_codiagram L M) n)
    (restricted_module_type phi (derived_limit B (mackey_codiagram L descended_mackey) n)) :=
  module_iso_comp (functor_iso (derived_limit_functor A (opposite D) n) descended_coefficient_iso)
    (iso_symm (scalar_higher_limit_iso phi (mackey_codiagram L descended_mackey) n)).

Theorem descended_higher_limit_zero_iff n :
  (forall q : derived_limit A (mackey_codiagram L M) n, q = 0) <->
  (forall q : derived_limit B (mackey_codiagram L descended_mackey) n, q = 0).
Proof. exact: module_iso_zero_iff (descended_higher_limit_iso n). Qed.

Theorem descended_mackey_bar_acyclic :
  mackey_bar_acyclic L descended_mackey -> mackey_bar_acyclic L M.
Proof.
move=> h; apply/(bar_derived_positive_zero_iff (mackey_codiagram L M)) => n.
apply/(descended_higher_limit_zero_iff n.+1).
exact (proj1 (bar_derived_positive_zero_iff (mackey_codiagram L descended_mackey)) h n).
Qed.

End Descent.
End DPBarScalarDescent.
