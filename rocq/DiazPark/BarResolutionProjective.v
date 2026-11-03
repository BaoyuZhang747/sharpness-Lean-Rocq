From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  BarComplex BarResolutionTerms BarResolutionHom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarComplex DiazParkBarResolutionTerms
  DiazParkBarResolutionHom.
Local Open Scope ring_scope.

(** Actual lifting of a natural transformation from each bar term through
    every pointwise-surjective coefficient morphism.  The lift is natural,
    rather than a family of unrelated objectwise module lifts. *)
Module DiazParkBarResolutionProjective.

Section Projectivity.
Variable R : pzRingType.
Variable C : category.
Variables D E : module_codiagram R C.
Variable q : nat_trans D E.
Hypothesis q_surjective : forall x (v : fobj E x),
  exists w : fobj D x, module_hom_fun (component q x) w = v.

Theorem resolution_term_lift n (alpha : nat_trans (@resolution_term R C n) E) :
  exists beta : nat_trans (@resolution_term R C n) D, nat_comp beta q = alpha.
Proof.
pose a : bar_term D n := fun x p => proj1_sig
  (constructive_indefinite_description
    (@q_surjective x (@term_to_cochain R C E n alpha x p))).
exists (cochain_to_term a).
apply term_to_cochain_injective.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (module_hom_fun (component q x)
    (@term_to_cochain R C D n (cochain_to_term a) x p) =
  @term_to_cochain R C E n alpha x p).
rewrite term_cochain_inverse /a.
exact: (proj2_sig (constructive_indefinite_description
  (@q_surjective x (@term_to_cochain R C E n alpha x p)))).
Qed.

End Projectivity.
End DiazParkBarResolutionProjective.
