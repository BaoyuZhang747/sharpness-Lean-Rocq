From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra rat.
From DiazPark Require Import PrimeLocalRing PrimeLocalIntegers.
Import GRing.Theory Num.Theory DPPrimeLocal DPPrimeLocalIntegers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPPrimeLocalUniversal.

(** Invertibility here is an actual equation, meaningful also in the zero ring. *)
Definition primes_inverted (p : nat) (R : comPzRingType) : Prop :=
  forall n : nat, coprime p n -> exists u : R, u * n%:R = 1.

Section Universal.
Variable p : nat.
Variable R : comPzRingType.
Hypothesis localR : primes_inverted p R.
Local Notation Zp := (DPPrimeLocal.type p).
Local Notation N x := (numq (DPPrimeLocal.value x)).
Local Notation D x := (denq (DPPrimeLocal.value x)).

Lemma denominator_inverse_exists (x : Zp) : exists u : R, u * (D x)%:~R == 1.
Proof.
have [u hu] := @localR (absz (D x)) (valP x).
exists u; apply/eqP.
have ed : ((absz (D x))%:Z) = D x by rewrite gez0_abs ?denq_ge0.
by rewrite -ed.
Qed.

Definition denominator_inverse (x : Zp) : R := xchoose (denominator_inverse_exists x).

Lemma denominator_inverse_spec (x : Zp) : denominator_inverse x * (D x)%:~R = 1.
Proof. apply/eqP; exact: (xchooseP (denominator_inverse_exists x)). Qed.

Definition scalar_map (x : Zp) : R := (N x)%:~R * denominator_inverse x.

Lemma scalar_map_denominator (x : Zp) : scalar_map x * (D x)%:~R = (N x)%:~R.
Proof. by rewrite /scalar_map -mulrA denominator_inverse_spec mulr1. Qed.

Lemma inverse_cancels_right (d u : R) : u * d = 1 ->
  forall a b : R, a * d = b * d -> a = b.
Proof.
move=> hu a b e; have h := congr1 (fun z => z * u) e.
by rewrite -!mulrA [d * u]mulrC hu !mulr1 in h.
Qed.

Lemma scalar_map_integral_relation (x : Zp) (n d : int) :
  DPPrimeLocal.value x * d%:~R = n%:~R -> scalar_map x * d%:~R = n%:~R.
Proof.
move=> e.
have cross : N x * d = n * D x.
  apply: (@intr_inj [the numDomainType of (rat : Type)]).
  by rewrite !intrM numqE mulrAC e.
apply: (inverse_cancels_right (denominator_inverse_spec x)).
rewrite mulrAC scalar_map_denominator -!intrM cross.
by [].
Qed.

Lemma scalar_map_integer (n : int) : scalar_map (n%:~R : Zp) = n%:~R.
Proof.
have h := @scalar_map_integral_relation (n%:~R : Zp) n 1.
rewrite value_int mulr1 in h.
by have := h erefl; rewrite mulr1.
Qed.

Lemma scalar_map_one : scalar_map 1 = 1.
Proof. exact: scalar_map_integer 1. Qed.

Lemma scalar_map_additive : additive scalar_map.
Proof.
move=> x y.
have ex : DPPrimeLocal.value (x-y) * (D x * D y)%:~R =
    (N x * D y - N y * D x)%:~R.
  change ((DPPrimeLocal.value x - DPPrimeLocal.value y) * (D x * D y)%:~R =
    (N x * D y - N y * D x)%:~R).
  rewrite intrB !intrM mulrBl !mulrA.
  by rewrite -numqE [DPPrimeLocal.value y * (D x)%:~R * (D y)%:~R]mulrAC -numqE.
have eq := scalar_map_integral_relation ex.
have invprod : (denominator_inverse x * denominator_inverse y) * (D x * D y)%:~R = 1.
  by rewrite intrM mulrACA !denominator_inverse_spec mulr1.
apply: (inverse_cancels_right invprod).
rewrite eq intrB !intrM mulrBl !mulrA scalar_map_denominator.
by rewrite [scalar_map y * (D x)%:~R * (D y)%:~R]mulrAC scalar_map_denominator.
Qed.

HB.instance Definition _ := GRing.isAdditive.Build Zp R scalar_map scalar_map_additive.

Lemma scalar_map_mul x y : scalar_map (x*y) = scalar_map x * scalar_map y.
Proof.
have ex : DPPrimeLocal.value (x*y) * (D x * D y)%:~R = (N x * N y)%:~R.
  change ((DPPrimeLocal.value x * DPPrimeLocal.value y) * (D x * D y)%:~R = (N x * N y)%:~R).
  by rewrite !intrM mulrACA -!numqE.
have eq := scalar_map_integral_relation ex.
have invprod : (denominator_inverse x * denominator_inverse y) * (D x * D y)%:~R = 1.
  by rewrite intrM mulrACA !denominator_inverse_spec mulr1.
apply: (inverse_cancels_right invprod).
by rewrite eq !intrM mulrACA !scalar_map_denominator.
Qed.

Lemma scalar_map_monoid : monoid_morphism scalar_map.
Proof. split; [exact: scalar_map_one | exact: scalar_map_mul]. Qed.

HB.instance Definition _ := GRing.isMonoidMorphism.Build Zp R scalar_map scalar_map_monoid.

Definition canonical_map : {rmorphism Zp -> R} := scalar_map.

Lemma canonical_map_unique (f : {rmorphism Zp -> R}) : f =1 canonical_map.
Proof.
move=> x; apply: (inverse_cancels_right (denominator_inverse_spec x)).
rewrite scalar_map_denominator -(rmorph_int f (D x)) -rmorphM.
have ex : x * (D x)%:~R = (N x)%:~R.
  apply: DPPrimeLocal.value_injective.
  change (DPPrimeLocal.value x * DPPrimeLocal.value ((D x)%:~R : Zp) =
    DPPrimeLocal.value ((N x)%:~R : Zp)).
  by rewrite !value_int numqE.
by rewrite ex rmorph_int.
Qed.

End Universal.
End DPPrimeLocalUniversal.




