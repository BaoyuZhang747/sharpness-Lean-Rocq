(** An ordinary adjunction yields the full coefficient-natural higher-limit
    comparison. Restriction is exact, and its actual adjunction proves
    injective preservation. No derived comparison is assumed. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryExtensionality CategoryAdjunction
  CategoryPrecompositionAdjunction CategoryModules CategoryInjectives ModuleDiagrams
  CategoryModuleLimitFunctor CategoryResolutionTransport CategoryDerivedTransport
  CategoryDerivedLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Restriction.
Variable R : pzRingType.
Variables C D : category.
Variable L : functor C D.

Lemma module_restriction_preserves_zero :
    diagram_functor_preserves_zero (precomposition (module_category R) L).
Proof. intros F G x v; reflexivity. Qed.

Lemma module_restriction_preserves_exact :
    diagram_functor_preserves_exact (precomposition (module_category R) L).
Proof. intros F G H a b he x v; exact (he (fobj L x) v). Qed.

Lemma module_restriction_preserves_injections :
    diagram_functor_preserves_injections (precomposition (module_category R) L).
Proof. intros F G a ha x; exact (ha (fobj L x)). Qed.

Variable U : functor D C.
Variable a : adjunction L U.

Theorem left_adjoint_restriction_preserves_injectives (F : module_diagram R D) :
    injective_object (functor_category D (module_category R)) F ->
    injective_object (functor_category C (module_category R)) (functor_comp L F).
Proof.
apply (right_adjoint_preserves_injectives (precomposition_adjunction (module_category R) a)).
exact (@module_precomposition_preserves_monomorphisms R D C U).
Qed.

Definition derived_left_adjoint_nat_iso (n : nat) : @isomorphism
    (functor_category (functor_category D (module_category R)) (module_category R))
    (derived_limit_functor R D n)
    (functor_comp (precomposition (module_category R) L) (derived_limit_functor R C n)) :=
  iso_symm (@derived_limit_transport_nat_iso R D C (precomposition (module_category R) L)
    module_restriction_preserves_zero (iso_symm (module_left_adjoint_limit_nat_iso R a))
    module_restriction_preserves_exact module_restriction_preserves_injections
    left_adjoint_restriction_preserves_injectives n).
End Restriction.

Arguments derived_left_adjoint_nat_iso R {C D L U} a n.
