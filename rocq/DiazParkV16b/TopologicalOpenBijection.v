(** A bijective continuous open map yields an actual homeomorphism. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical topology.
From DiazParkV16b Require Import TopologicalCategory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological.
Local Open Scope classical_set_scope.

Module DPTopologicalOpenBijection.
Section Bijection.
Variables X Y : topologicalType.
Variable f : continuousType X Y.
Variable hinj : injective f.
Variable hsurj : forall y, exists x, f x = y.
Variable hopen : forall S : set X, open S -> open (f @` S).
Definition open_bijection_inverse (y : Y) := proj1_sig (constructive_indefinite_description (hsurj y)).
Lemma open_bijection_inverseK : cancel open_bijection_inverse f.
Proof. move=> y; exact: (proj2_sig (constructive_indefinite_description (hsurj y))). Qed.
Lemma open_bijection_forwardK : cancel f open_bijection_inverse.
Proof. move=> x; apply: hinj; exact: open_bijection_inverseK. Qed.
Lemma open_bijection_inverse_continuous : continuous open_bijection_inverse.
Proof.
apply/continuousP => S hS.
have e : open_bijection_inverse @^-1` S = f @` S.
  apply/seteqP; split=> y.
  - move=> hy; exists (open_bijection_inverse y) => //; exact: open_bijection_inverseK.
  - move=> [x hx <-]; change (S (open_bijection_inverse (f x))); by rewrite open_bijection_forwardK.
rewrite e; exact: hopen hS.
Qed.
Definition open_bijection_homeomorphism : homeomorphism X Y :=
  homeomorphism_of_inverse (@cts_fun _ _ f) open_bijection_inverse_continuous
    open_bijection_forwardK open_bijection_inverseK.
End Bijection.
End DPTopologicalOpenBijection.
