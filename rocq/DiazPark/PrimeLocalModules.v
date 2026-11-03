From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra rat.
From DiazPark Require Import PrimeLocalRing PrimeLocalIntegers PrimeLocalUniversal.
Import GRing.Theory DPPrimeLocal DPPrimeLocalIntegers DPPrimeLocalUniversal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPPrimeLocalModules.
Section ScalarRestriction.
Variable p : nat.
Variable R : comPzRingType.
Variable phi : {rmorphism DPPrimeLocal.type p -> R}.
Variable V : lmodType R.
Local Notation Zp := (DPPrimeLocal.type p).

Definition restriction_type := let _ := phi in (V : Type).
HB.instance Definition _ := GRing.Zmodule.on restriction_type.

Definition restricted_scale (a : Zp) (x : restriction_type) := phi a *: (x : V).

Lemma restricted_scaleA a b x :
  restricted_scale a (restricted_scale b x) = restricted_scale (a*b) x.
Proof. by rewrite /restricted_scale scalerA rmorphM. Qed.

Lemma restricted_scale1 : left_id 1 restricted_scale.
Proof. by move=> x; rewrite /restricted_scale rmorph1 scale1r. Qed.

Lemma restricted_scaleDr : right_distributive restricted_scale +%R.
Proof. by move=> a x y; rewrite /restricted_scale scalerDr. Qed.

Lemma restricted_scaleDl x : {morph restricted_scale^~ x : a b / a+b}.
Proof. by move=> a b; rewrite /restricted_scale rmorphD scalerDl. Qed.

(** The carrier and additive operations are unchanged, and the action is the
    actual scalar action through phi. No nonzero-ring or dimension assumption. *)
HB.instance Definition _ := GRing.Zmodule_isLmodule.Build Zp restriction_type
  restricted_scaleA restricted_scale1 restricted_scaleDr restricted_scaleDl.

Definition restricted_module : lmodType Zp := [the lmodType Zp of restriction_type].

Lemma restricted_module_action a (x : restricted_module) : a *: x = phi a *: (x : V).
Proof. reflexivity. Qed.

Lemma restricted_integer_action (n : int) (x : restricted_module) :
  n%:~R *: x = (n%:~R : R) *: (x : V).
Proof. by rewrite restricted_module_action rmorph_int. Qed.

End ScalarRestriction.

Section LinearMaps.
Variable p : nat.
Variable R : comPzRingType.
Variable phi : {rmorphism DPPrimeLocal.type p -> R}.
Variables V W : lmodType R.
Variable f : {linear V -> W}.

Lemma restriction_linear :
  linear (f : restricted_module phi V -> restricted_module phi W).
Proof.
move=> a x y.
change (f (phi a *: x + y) = phi a *: f x + f y).
exact: linearP.
Qed.

Definition restricted_linear : {linear restricted_module phi V -> restricted_module phi W} :=
  HB.pack (f : restricted_module phi V -> restricted_module phi W) (GRing.isLinear.Build (DPPrimeLocal.type p)
    (restricted_module phi V) (restricted_module phi W) _ f restriction_linear).

End LinearMaps.

Section UniversalCriterion.
Variable p : nat.
Variable R : comPzRingType.

Lemma scalar_map_implies_primes_inverted (hp : prime p)
    (phi : {rmorphism DPPrimeLocal.type p -> R}) : primes_inverted p R.
Proof.
move=> n hn; exists (phi ((n%:R : DPPrimeLocal.type p)^-1)).
by rewrite -(rmorph_nat phi n) -rmorphM (@natural_inverse_mul p hp n hn) rmorph1.
Qed.

Theorem local_algebra_iff_inverts_primes (hp : prime p) :
  (exists phi : {rmorphism DPPrimeLocal.type p -> R}, True) <-> primes_inverted p R.
Proof.
split; first by move=> [phi _]; exact: scalar_map_implies_primes_inverted hp phi.
move=> h; exists (canonical_map h); exact I.
Qed.

End UniversalCriterion.
End DPPrimeLocalModules.



