From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryFinitePullbacks MackeyStructures MackeyPair
  PrimeLocalRing PrimeLocalModules.
Import GRing.Theory DPPrimeLocal DPPrimeLocalModules.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPPrimeLocalMackey.
Section Restriction.
Variable p : nat.
Variable R : comPzRingType.
Variable phi : {rmorphism DPPrimeLocal.type p -> R}.
Variable C : category.
Variable M : mackey_pair R C.

(** The modules have exactly the original carrier and additive operations;
    every pullback and transfer is exactly its original function. *)
Definition restrict_mackey_pair : mackey_pair (DPPrimeLocal.type p) C :=
  @MackeyPair (DPPrimeLocal.type p) C
    (fun P => restricted_module phi (pair_value M P))
    (fun P Q f => restricted_linear phi (pair_pull M f))
    (fun P Q f => restricted_linear phi (pair_push M f))
    (@pair_pull_id _ _ M) (@pair_push_id _ _ M)
    (@pair_pull_comp _ _ M) (@pair_push_comp _ _ M) (@pair_pull_iso _ _ M).

Lemma restrict_pull (P Q : C) (f : hom C P Q) x :
  pair_pull restrict_mackey_pair f x = pair_pull M f x.
Proof. reflexivity. Qed.

Lemma restrict_push (P Q : C) (f : hom C P Q) x :
  pair_push restrict_mackey_pair f x = pair_push M f x.
Proof. reflexivity. Qed.

Lemma restrict_sum (P : C) (I : finType) (v : I -> pair_value M P) :
  (\sum_i v i : pair_value restrict_mackey_pair P) = (\sum_i v i : pair_value M P).
Proof. reflexivity. Qed.

Lemma restrict_mackey_formula_iff (B : mackey_shape C) :
  pair_mackey_formula restrict_mackey_pair B <-> pair_mackey_formula M B.
Proof. reflexivity. Qed.

Lemma restrict_pullback_formula (P Q T : C) (f : hom C P T) (g : hom C Q T)
    (D : finite_pullback_decomposition f g) :
  (forall x, pair_pull M g (pair_push M f x) =
    \sum_(i : pb_index D) pair_push M (pb_right D i) (pair_pull M (pb_left D i) x)) ->
  forall x, pair_pull restrict_mackey_pair g (pair_push restrict_mackey_pair f x) =
    \sum_(i : pb_index D) pair_push restrict_mackey_pair (pb_right D i)
      (pair_pull restrict_mackey_pair (pb_left D i) x).
Proof. exact: id. Qed.

End Restriction.

Definition restrict_mackey_module (p : nat) (R : comPzRingType)
    (phi : {rmorphism DPPrimeLocal.type p -> R}) (C : category)
    (B : mackey_shape C) (M : mackey_module R B) :
    mackey_module (DPPrimeLocal.type p) B :=
  @mackey_module_of_pair (DPPrimeLocal.type p) C (restrict_mackey_pair phi (pair_of_mackey M)) B
    (@mackey_formula R C B M).

End DPPrimeLocalMackey.

