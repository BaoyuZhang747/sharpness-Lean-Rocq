(** The ordinary lifting definition of projectivity for actual modules.
    Free modules and finite products satisfy it; no projectivity is postulated. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import BarFreeModule.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule.
Local Open Scope ring_scope.

Module DPLinearProjective.
Section Projectivity.
Variable R : pzRingType.

Definition linear_projective (P : lmodType R) : Prop :=
  forall (M N : lmodType R) (q : {linear M -> N}),
    (forall y, exists x, q x = y) ->
    forall a : {linear P -> N}, exists b : {linear P -> M},
      forall x, q (b x) = a x.

Lemma free_projective (X : Type) : linear_projective (free_module R X).
Proof.
move=> M N q hq a.
pose chosen x := proj1_sig (constructive_indefinite_description (hq (a (free_basis R x)))).
have hc x : q (chosen x) = a (free_basis R x).
  exact: (proj2_sig (constructive_indefinite_description (hq (a (free_basis R x))))).
exists (free_lift chosen).
apply: (free_lift_ext (g := (q \o free_lift chosen : {linear _ -> _})) (h := a)).
by move=> x; rewrite /= free_lift_basis hc.
Qed.

Lemma retract_projective (P Q : lmodType R)
    (i : {linear P -> Q}) (r : {linear Q -> P}) :
    (forall x, r (i x) = x) -> linear_projective Q -> linear_projective P.
Proof.
move=> hir hQ M N q hq a.
have [b hb] := hQ M N q hq (a \o r : {linear Q -> N}).
exists (b \o i : {linear P -> M}); by move=> x; rewrite /= hb /= hir.
Qed.

Definition product_left (P Q : lmodType R) (x : P) : (P * Q)%type := (x,0).
Definition product_right (P Q : lmodType R) (x : Q) : (P * Q)%type := (0,x).
Lemma product_left_linear (P Q : lmodType R) : linear (@product_left P Q).
Proof. move=> r x y; change ((r *: x + y, (0 : Q)) = (r *: x + y, r *: 0 + 0)); by rewrite scaler0 addr0. Qed.
Lemma product_right_linear (P Q : lmodType R) : linear (@product_right P Q).
Proof. move=> r x y; change (((0 : P), r *: x + y) = (r *: 0 + 0, r *: x + y)); by rewrite scaler0 addr0. Qed.
HB.instance Definition _ P Q := GRing.isLinear.Build R _ _ _ (@product_left P Q) (@product_left_linear P Q).
HB.instance Definition _ P Q := GRing.isLinear.Build R _ _ _ (@product_right P Q) (@product_right_linear P Q).

Definition product_lift (P Q M : lmodType R)
    (a : {linear P -> M}) (b : {linear Q -> M}) (x : P * Q) := a x.1 + b x.2.
Lemma product_lift_linear (P Q M : lmodType R)
    (a : {linear P -> M}) (b : {linear Q -> M}) : linear (product_lift a b).
Proof.
move=> r [x y] [z t]; change (a (r *: x + z) + b (r *: y + t) =
  r *: (a x + b y) + (a z + b t)).
by rewrite !linearP scalerDr addrACA.
Qed.
HB.instance Definition _ P Q M a b :=
  GRing.isLinear.Build R _ _ _ (@product_lift P Q M a b) (@product_lift_linear P Q M a b).

Lemma product_projective (P Q : lmodType R) :
    linear_projective P -> linear_projective Q ->
    linear_projective [the lmodType R of (P * Q)%type].
Proof.
move=> hP hQ M N q hq a.
have [b hb] := hP M N q hq (a \o (@product_left P Q) : {linear P -> N}).
have [c hc] := hQ M N q hq (a \o (@product_right P Q) : {linear Q -> N}).
exists (product_lift b c); move=> [x y].
rewrite /product_lift /= linearD hb hc /= -linearD.
change (a (x + 0, 0 + y) = a (x,y)); by rewrite addr0 add0r.
Qed.
End Projectivity.
End DPLinearProjective.
