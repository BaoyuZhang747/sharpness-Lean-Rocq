(** The genuine finite-diagonal total of a first-quadrant bicomplex.
    The degree n product has precisely the components p+q=n. The vertical
    differential carries the sign (-1)^p; no convergence hypothesis is used. *)
From Coq Require Import Arith.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import CategoryModuleProducts HomologicalComplex.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFirstQuadrantCochain DiazParkHomological.
Local Open Scope ring_scope.

Module DPFirstQuadrantTotal.
Section Total.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition total_term n : lmodType R :=
  module_product_type (fun p : nat => module_product_type (fun q : nat =>
    module_product_type (fun _ : (p + q)%coq_nat = n => bicomplex_term K p q))).

Lemma horizontal_index p q n : (p.+1 + q)%coq_nat = n.+1 -> (p + q)%coq_nat = n.
Proof. exact (@Nat.succ_inj _ _). Qed.

Lemma vertical_index p q n : (p + q.+1)%coq_nat = n.+1 -> (p + q)%coq_nat = n.
Proof. rewrite Nat.add_succ_r. exact (@Nat.succ_inj _ _). Qed.

Definition total_horizontal n (a : total_term n) : total_term n.+1 :=
  fun p => match p as k return forall q, (k + q)%coq_nat = n.+1 -> bicomplex_term K k q with
  | 0%N => fun q h => 0
  | k.+1 => fun q h => horizontal K k q (a k q (horizontal_index h))
  end.

Definition total_vertical n (a : total_term n) : total_term n.+1 :=
  fun p q => match q as k return (p + k)%coq_nat = n.+1 -> bicomplex_term K p k with
  | 0%N => fun h => 0
  | k.+1 => fun h => (-1 : R) ^+ p *: vertical K p k (a p k (vertical_index h))
  end.

Lemma total_horizontal_linear n : linear (@total_horizontal n).
Proof.
intros r a b; apply functional_extensionality_dep; intro p.
apply functional_extensionality_dep; intro q.
apply functional_extensionality_dep; intro h.
destruct p as [|p]; cbn [total_horizontal].
- change (0 = r *: (0 : bicomplex_term K 0%N q) + 0).
  by rewrite scaler0 addr0.
- change (horizontal K p q (r *: a p q (horizontal_index h) + b p q (horizontal_index h)) =
    r *: horizontal K p q (a p q (horizontal_index h)) + horizontal K p q (b p q (horizontal_index h))).
  exact: linearP.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (total_term n) (total_term n.+1)
  _ (@total_horizontal n) (@total_horizontal_linear n).

Lemma total_vertical_linear n : linear (@total_vertical n).
Proof.
intros r a b; apply functional_extensionality_dep; intro p.
apply functional_extensionality_dep; intro q.
apply functional_extensionality_dep; intro h.
destruct q as [|q]; cbn [total_vertical].
- change (0 = r *: (0 : bicomplex_term K p 0%N) + 0).
  by rewrite scaler0 addr0.
- change ((-1 : R)^+p *: vertical K p q (r *: a p q (vertical_index h) + b p q (vertical_index h)) =
    r *: ((-1 : R)^+p *: vertical K p q (a p q (vertical_index h))) +
    (-1 : R)^+p *: vertical K p q (b p q (vertical_index h))).
  by rewrite linearP scalerDr !scalerA commr_sign.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (total_term n) (total_term n.+1)
  _ (@total_vertical n) (@total_vertical_linear n).

Lemma total_horizontal_squared n (a : total_term n) :
    total_horizontal (total_horizontal a) = 0.
Proof.
apply functional_extensionality_dep; intro p.
apply functional_extensionality_dep; intro q.
apply functional_extensionality_dep; intro h.
destruct p as [|[|p]]; cbn [total_horizontal].
- reflexivity.
- exact: linear0.
- exact: horizontal_squared.
Qed.

Lemma total_vertical_squared n (a : total_term n) :
    total_vertical (total_vertical a) = 0.
Proof.
apply functional_extensionality_dep; intro p.
apply functional_extensionality_dep; intro q.
apply functional_extensionality_dep; intro h.
destruct q as [|[|q]]; cbn [total_vertical].
- reflexivity.
- by rewrite linear0 scaler0.
- rewrite linearZ vertical_squared.
  change ((-1 : R)^+p *: ((-1 : R)^+p *: (0 : bicomplex_term K p q.+2)) = 0).
  by rewrite !scaler0.
Qed.

Lemma total_mixed_cancel n (a : total_term n) :
    total_horizontal (total_vertical a) + total_vertical (total_horizontal a) = 0.
Proof.
apply functional_extensionality_dep; intro p.
apply functional_extensionality_dep; intro q.
apply functional_extensionality_dep; intro h.
destruct p as [|p]; destruct q as [|q]; cbn [total_horizontal total_vertical].
- exact: add0r.
- change (0 + (-1 : R)^+0 *: vertical K 0%N q 0 = 0).
  by rewrite linear0 scaler0 addr0.
- change (horizontal K p 0%N 0 + 0 = 0).
  by rewrite linear0 addr0.
- change (horizontal K p q.+1
    ((-1 : R)^+p *: vertical K p q
      (a p q (vertical_index (horizontal_index h)))) +
    (-1 : R)^+p.+1 *: vertical K p.+1 q
      (horizontal K p q (a p q (horizontal_index (vertical_index h)))) = 0).
  have he : vertical_index (horizontal_index h) = horizontal_index (vertical_index h)
    by apply Prop_irrelevance.
  rewrite he linearZ horizontal_vertical exprS mulN1r scaleNr.
  exact: subrr.
Qed.

Definition total_d n (a : total_term n) : total_term n.+1 :=
  total_horizontal a + total_vertical a.

Lemma total_d_linear n : linear (@total_d n).
Proof. move=> r a b; by rewrite /total_d !linearP scalerDr addrACA. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (total_term n) (total_term n.+1)
  _ (@total_d n) (@total_d_linear n).

Lemma total_d_squared n (a : total_term n) : total_d (total_d a) = 0.
Proof.
rewrite /total_d !linearD.
change (total_horizontal (total_horizontal a) + total_horizontal (total_vertical a) +
  (total_vertical (total_horizontal a) + total_vertical (total_vertical a)) = 0).
rewrite total_horizontal_squared total_vertical_squared add0r addr0.
exact: total_mixed_cancel.
Qed.

Definition total_complex : cochain_complex R :=
  @CochainComplex R total_term (fun n => (@total_d n : {linear _ -> _})) total_d_squared.
End Total.
End DPFirstQuadrantTotal.
