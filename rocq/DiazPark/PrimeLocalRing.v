From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra rat.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPPrimeLocal.
Section LocalIntegers.
Variable p : nat.

(** The actual rational subring Z_(p), using reduced rational denominators. *)
Definition local_pred (x : rat) := coprime p `|denq x|.

Lemma local_integer (n : int) : local_pred n%:~R.
Proof. by rewrite /local_pred denq_int /= coprimen1. Qed.

Lemma local_fraction (n d : int) : coprime p `|d| -> local_pred (n%:~R / d%:~R).
Proof.
case: (divqP n d)=> [h0|k x hk]; first by move=> _; exact: local_integer 0.
by rewrite /local_pred abszM coprimeMr=> /andP[_].
Qed.

Lemma local_opp x : local_pred x -> local_pred (-x).
Proof.
move=> hx; change (local_pred (oppq x)).
rewrite oppq_def fracqE /=; exact: local_fraction hx.
Qed.

Lemma local_add x y : local_pred x -> local_pred y -> local_pred (x + y).
Proof.
move=> hx hy; change (local_pred (addq x y)).
rewrite addq_def addq_subdefE fracqE /=.
apply: local_fraction; by rewrite abszM coprimeMr; apply/andP.
Qed.

Lemma local_mul x y : local_pred x -> local_pred y -> local_pred (x * y).
Proof.
move=> hx hy; change (local_pred (mulq x y)).
rewrite mulq_def mulq_subdefE fracqE /=.
apply: local_fraction; by rewrite abszM coprimeMr; apply/andP.
Qed.

Lemma local_subring : subring_closed local_pred.
Proof.
split; first exact: local_integer 1.
- move=> x y hx hy; exact: local_add hx (local_opp hy).
- exact: local_mul.
Qed.

HB.instance Definition _ := GRing.isSubringClosed.Build rat local_pred local_subring.

Record type := Local { value : rat; _ : local_pred value }.
HB.instance Definition _ := [isSub for value].
HB.instance Definition _ := [Choice of type by <:].
HB.instance Definition _ := [SubChoice_isSubComNzRing of type by <:].

Lemma value_injective : injective value.
Proof. exact: val_inj. Qed.

Definition unit_pred (x : type) := (value x != 0) && local_pred (value x)^-1.

Definition inverse (x : type) : type :=
  if unit_pred x then insubd x (value x)^-1 else x.

Lemma inverse_unit x : unit_pred x -> value (inverse x) = (value x)^-1.
Proof.
move=> hx; rewrite /inverse hx /insubd; case: insubP=> [y hy ey|hy]; first exact ey.
by move: (andP hx).2; rewrite (negPf hy).
Qed.

Lemma inverse_out : {in [predC unit_pred], inverse =1 id}.
Proof.
move=> x hx; have hn : unit_pred x = false := negPf hx.
by rewrite /inverse hn.
Qed.

Lemma inverse_mul : {in unit_pred, left_inverse 1 inverse *%R}.
Proof.
move=> x hx; apply: value_injective.
change (value (inverse x) * value x = 1).
rewrite inverse_unit // mulVf //; exact: (andP hx).1.
Qed.

Lemma unit_of_inverse x y : y * x = 1 -> unit_pred x.
Proof.
move=> hy; have e := congr1 value hy.
change (value y * value x = 1) in e.
have nx : value x != 0.
  apply/negP=> /eqP ex; by move: e; rewrite ex mulr0 => /eqP; rewrite eq_sym oner_eq0.
apply/andP; split=> //.
have ev : (value x)^-1 = value y.
  apply: (mulfI nx); by rewrite mulfV // mulrC e.
rewrite ev; exact: valP y.
Qed.

HB.instance Definition _ := GRing.ComNzRing_hasMulInverse.Build type
  inverse_mul unit_of_inverse inverse_out.

Lemma integral_axiom (x y : type) : x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> he; have e := congr1 value he.
change (value x * value y = 0) in e.
have /orP[hx|hy] : (value x == 0) || (value y == 0).
  by rewrite -mulf_eq0; apply/eqP.
- apply/orP; left; apply/eqP; apply: value_injective; change (value x = 0); exact: eqP hx.
- apply/orP; right; apply/eqP; apply: value_injective; change (value y = 0); exact: eqP hy.
Qed.

HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build type integral_axiom.

End LocalIntegers.
Arguments value {p} _.
End DPPrimeLocal.








