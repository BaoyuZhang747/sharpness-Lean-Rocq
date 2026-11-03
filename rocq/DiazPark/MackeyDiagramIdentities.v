(** Exact identifications of the paired and full-module coefficient diagrams. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryIsomorphism CategoryModules
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyBarReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Identities.
Variable R : comPzRingType.
Variables C D : category.
Variable L : functor D C.

Lemma pair_restrict_codiagram (M : mackey_pair R C) :
  pair_codiagram (pair_restrict M L) = functor_comp (functor_op L) (pair_codiagram M).
Proof.
apply (@functor_extensionality (opposite D) (module_category R)
  (pair_codiagram (pair_restrict M L))
  (functor_comp (functor_op L) (pair_codiagram M)) (Logic.eq_refl _)).
reflexivity.
Qed.

Lemma native_pair_codiagram (B : mackey_shape C) (M : mackey_module R B) :
  mackey_codiagram L M = pair_codiagram (pair_restrict (pair_of_mackey M) L).
Proof.
apply (@functor_extensionality (opposite D) (module_category R)
  (mackey_codiagram L M) (pair_codiagram (pair_restrict (pair_of_mackey M) L))
  (Logic.eq_refl _)).
reflexivity.
Qed.

Lemma of_pair_codiagram (M : mackey_pair R C) (B : mackey_shape C)
    (h : pair_mackey_formula M B) :
  mackey_codiagram L (mackey_module_of_pair h) = pair_codiagram (pair_restrict M L).
Proof.
apply (@functor_extensionality (opposite D) (module_category R)
  (mackey_codiagram L (mackey_module_of_pair h)) (pair_codiagram (pair_restrict M L))
  (Logic.eq_refl _)).
reflexivity.
Qed.
End Identities.
