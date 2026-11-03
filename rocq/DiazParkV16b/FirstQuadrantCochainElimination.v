(** Finite elimination of a total cocycle supported away from column zero.
    The induction stops because only a finite diagonal exists in each degree. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import HomologicalComplex.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalSupport FirstQuadrantCochainEdge FirstQuadrantCochainLeading
  FirstQuadrantCochainCorrection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFirstQuadrantCochain DPFirstQuadrantTotal
  DPFirstQuadrantSupport DPFirstQuadrantEdge DPFirstQuadrantLeading DPFirstQuadrantCorrection.
Local Open Scope ring_scope.

Module DPFirstQuadrantElimination.
Section Elimination.
Variable R : pzRingType.
Variable K : bicomplex R.
Variable hK : positive_horizontal_exact K.

Lemma supported_from_sub n (x y : total_term K n) p :
    supported_from x p -> supported_from y p -> supported_from (x - y) p.
Proof.
intros hx hy r s h hr.
change (x r s h - y r s h = 0).
by rewrite (hx r s h hr) (hy r s h hr) subrr.
Qed.

Lemma corrected_support n p q (hpq : (p + q)%coq_nat = n)
    (x : total_term K n.+1) (y : total_term K n)
    (hx : supported_from x p.+1) (hy : supported_from (total_d y) p.+1)
    (he : @total_d R K n y p.+1 q (horizontal_output_index hpq) =
      x p.+1 q (horizontal_output_index hpq)) :
    supported_from (x - total_d y) p.+2.
Proof.
intros r s h hr.
destruct (Nat.lt_ge_cases r p.+1) as [hrp|hrp].
- exact (@supported_from_sub n.+1 x (total_d y) p.+1 hx hy r s h hrp).
- have er : r = p.+1 by lia. subst r.
  have es : s = q by lia. subst s.
  have eh : h = horizontal_output_index hpq by apply Prop_irrelevance.
  change (x p.+1 q h - @total_d R K n y p.+1 q h = 0).
  by rewrite eh he subrr.
Qed.

Lemma corrected_cocycle n (x : total_term K n.+1) (y : total_term K n) :
    cocycle (total_complex K) n.+1 x ->
    cocycle (total_complex K) n.+1 (x - total_d y).
Proof.
intro hx; change (total_d (x - total_d y) = 0).
rewrite linearB.
change (total_d x - total_d (total_d y) = 0).
by rewrite total_d_squared subr0.
Qed.

Lemma tail_cycle_boundary_bounded k :
    forall n p, (n.+1 <= p + k)%coq_nat ->
    forall x : total_term K n.+1, cocycle (total_complex K) n.+1 x ->
      supported_from x p.+1 ->
      exists y : total_term K n, total_d y = x /\ supported_from y p.
Proof.
induction k as [|k IH]; intros n p hk x hx hs.
- have hzero : x = 0.
    apply supported_past_diagonal_zero.
    apply (supported_from_mono hs).
    apply le_n_S. rewrite addn0 in hk. exact hk.
  exists 0; split; [by rewrite linear0 hzero|exact: supported_from_zero].
- destruct (le_dec n.+1 p) as [hnp|hnp].
  + have hzero : x = 0.
      apply supported_past_diagonal_zero.
      apply (supported_from_mono hs); exact (le_n_S _ _ hnp).
    exists 0; split; [by rewrite linear0 hzero|exact: supported_from_zero].
  + have hpq : (p + Nat.sub n p)%coq_nat = n by lia.
    have [y [hy [hdy he]]] := @leading_correction R K hK n p (Nat.sub n p) hpq x hx hs.
    have hbound : (n.+1 <= p.+1 + k)%coq_nat.
      rewrite addSn. rewrite addnS in hk. exact hk.
    have [z [hz hzs]] := IH n p.+1 hbound (x - total_d y)
      (corrected_cocycle y hx) (@corrected_support n p (Nat.sub n p) hpq x y hs hdy he).
    exists (y + z); split.
    * rewrite linearD.
      change (total_d y + total_d z = x).
      by rewrite hz addrC subrK.
    * apply supported_from_add; [exact hy|].
      apply (supported_from_mono hzs); lia.
Qed.

Theorem tail_cycle_boundary n p (x : total_term K n.+1)
    (hx : cocycle (total_complex K) n.+1 x) (hs : supported_from x p.+1) :
    exists y : total_term K n, total_d y = x /\ supported_from y p.
Proof.
apply (@tail_cycle_boundary_bounded n.+1 n p); [|exact hx|exact hs].
apply/leP; exact: leq_addl.
Qed.
End Elimination.
End DPFirstQuadrantElimination.
