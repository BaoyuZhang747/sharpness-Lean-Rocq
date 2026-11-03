(** Literal differential components of a single diagonal summand, and
    the support gain when that summand is a vertical cocycle. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import HomologicalComplex.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps FirstQuadrantCochainTotalSupport FirstQuadrantCochainLeading.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFirstQuadrantCochain DPFirstQuadrantTotal
  DPFirstQuadrantTotalMaps DPFirstQuadrantSupport DPFirstQuadrantLeading.
Local Open Scope ring_scope.

Module DPFirstQuadrantInclusion.
Section Inclusion.
Variable R : pzRingType.
Variable K : bicomplex R.

Lemma include_d_horizontal p q n (hpq : (p + q)%coq_nat = n) (x : bicomplex_term K p q) :
    @total_d R K n (total_include hpq x) p.+1 q (horizontal_output_index hpq) =
      horizontal K p q x.
Proof.
destruct q as [|q].
- change (horizontal K p 0%N
    (@total_include R K p 0%N n hpq x p 0%N (horizontal_index (horizontal_output_index hpq))) + 0 =
      horizontal K p 0%N x).
  by rewrite total_include_same addr0.
- change (horizontal K p q.+1
    (@total_include R K p q.+1 n hpq x p q.+1 (horizontal_index (horizontal_output_index hpq))) +
    (-1 : R)^+p.+1 *: vertical K p.+1 q
      (@total_include R K p q.+1 n hpq x p.+1 q (vertical_index (horizontal_output_index hpq))) =
    horizontal K p q.+1 x).
  rewrite total_include_same total_include_other; [|lia].
  by rewrite linear0 scaler0 addr0.
Qed.

Lemma include_d_vertical p q n (hpq : (p + q)%coq_nat = n) (x : bicomplex_term K p q) :
    @total_d R K n (total_include hpq x) p q.+1 (vertical_output_index hpq) =
      (-1 : R)^+p *: vertical K p q x.
Proof.
destruct p as [|p].
- change (0 + (-1 : R)^+0 *: vertical K 0%N q
    (@total_include R K 0%N q n hpq x 0%N q (vertical_index (vertical_output_index hpq))) =
    (-1 : R)^+0 *: vertical K 0%N q x).
  by rewrite total_include_same add0r.
- change (horizontal K p q.+1
    (@total_include R K p.+1 q n hpq x p q.+1 (horizontal_index (vertical_output_index hpq))) +
    (-1 : R)^+p.+1 *: vertical K p.+1 q
      (@total_include R K p.+1 q n hpq x p.+1 q (vertical_index (vertical_output_index hpq))) =
    (-1 : R)^+p.+1 *: vertical K p.+1 q x).
  rewrite total_include_same total_include_other; [|lia].
  by rewrite linear0 add0r.
Qed.

Lemma include_cycle_d_supported p q n (hpq : (p + q)%coq_nat = n)
    (x : bicomplex_term K p q) (hx : cocycle (vertical_complex K p) q x) :
    supported_from (total_d (total_include hpq x)) p.+1.
Proof.
intros r s h hr.
have hor : (r < p)%coq_nat \/ r = p by lia.
destruct hor as [hrp|hrp].
- exact (@total_d_supported R K n (total_include hpq x) p
    (total_include_supported hpq x) r s h hrp).
- subst r.
  have hes : s = q.+1 by lia. subst s.
  have heh : h = vertical_output_index hpq by apply Prop_irrelevance.
  rewrite heh include_d_vertical.
  change (vertical K p q x = 0) in hx.
  by rewrite hx scaler0.
Qed.
End Inclusion.
End DPFirstQuadrantInclusion.
