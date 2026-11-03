(** The actual outgoing horizontal and vertical boundaries of a single total coordinate. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazParkV16b Require Import FirstQuadrantChainBicomplex FirstQuadrantChainTotal
  FirstQuadrantChainTotalSupport FirstQuadrantCochainTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFirstQuadrantChain DPFirstQuadrantChainTotal DPFirstQuadrantChainSupport.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainTotalInclusionDifferential.
Section Differential.
Variable R : pzRingType.
Variable K : bicomplex R.
Definition horizontal_boundary n (a : total_term K n.+1) : total_term K n :=
  fun p q h => horizontal K p q (a p.+1 q (horizontal_input h)).
Definition vertical_boundary n (a : total_term K n.+1) : total_term K n :=
  fun p q h => (-1:R)^+p *: vertical K p q (a p q.+1 (vertical_input h)).
Lemma total_d_split n (a : total_term K n.+1) :
  total_d a = horizontal_boundary a + vertical_boundary a.
Proof. reflexivity. Qed.

Theorem horizontal_boundary_include_zero q n (h : (0+q)%coq_nat=n.+1) x :
  horizontal_boundary (@total_include R K 0 q n.+1 h x) = 0.
Proof.
apply functional_extensionality_dep => r; apply functional_extensionality_dep => s;
  apply functional_extensionality_dep => hr.
change (horizontal K r s (@total_include R K 0 q n.+1 h x r.+1 s (horizontal_input hr)) = 0).
rewrite total_include_other; [exact: linear0|lia].
Qed.
Theorem horizontal_boundary_include_succ p q n (h : (p.+1+q)%coq_nat=n.+1) x :
  horizontal_boundary (@total_include R K p.+1 q n.+1 h x) =
    @total_include R K p q n (DPFirstQuadrantTotal.horizontal_index h) (horizontal K p q x).
Proof.
apply functional_extensionality_dep => r; apply functional_extensionality_dep => s;
  apply functional_extensionality_dep => hr.
change (horizontal K r s (@total_include R K p.+1 q n.+1 h x r.+1 s (horizontal_input hr)) =
  @total_include R K p q n (DPFirstQuadrantTotal.horizontal_index h) (horizontal K p q x) r s hr).
case: (Nat.eq_dec p r) => [e|e].
- subst r.
  have es : s=q by lia.
  subst s; by rewrite !total_include_same.
- have es : p.+1 <> r.+1 by lia.
  rewrite (@total_include_other R K p.+1 q n.+1 h x r.+1 s (horizontal_input hr) es).
  rewrite (@total_include_other R K p q n (DPFirstQuadrantTotal.horizontal_index h) (horizontal K p q x) r s hr e).
  exact: linear0.
Qed.
Theorem vertical_boundary_include_zero p n (h : (p+0)%coq_nat=n.+1) x :
  vertical_boundary (@total_include R K p 0 n.+1 h x) = 0.
Proof.
apply functional_extensionality_dep => r; apply functional_extensionality_dep => s;
  apply functional_extensionality_dep => hr.
change ((-1:R)^+r *: vertical K r s (@total_include R K p 0 n.+1 h x r s.+1 (vertical_input hr)) = 0).
rewrite total_include_other; [by rewrite linear0 scaler0|lia].
Qed.
Theorem vertical_boundary_include_succ p q n (h : (p+q.+1)%coq_nat=n.+1) x :
  vertical_boundary (@total_include R K p q.+1 n.+1 h x) =
    (-1:R)^+p *: @total_include R K p q n (DPFirstQuadrantTotal.vertical_index h) (vertical K p q x).
Proof.
apply functional_extensionality_dep => r; apply functional_extensionality_dep => s;
  apply functional_extensionality_dep => hr.
change ((-1:R)^+r *: vertical K r s (@total_include R K p q.+1 n.+1 h x r s.+1 (vertical_input hr)) =
  (-1:R)^+p *: @total_include R K p q n (DPFirstQuadrantTotal.vertical_index h) (vertical K p q x) r s hr).
case: (Nat.eq_dec p r) => [e|e].
- subst r.
  have es : s=q by lia.
  subst s; by rewrite !total_include_same.
- rewrite (@total_include_other R K p q.+1 n.+1 h x r s.+1 (vertical_input hr) e).
  rewrite (@total_include_other R K p q n (DPFirstQuadrantTotal.vertical_index h) (vertical K p q x) r s hr e).
  by rewrite linear0 !scaler0.
Qed.
End Differential.
End DPFirstQuadrantChainTotalInclusionDifferential.
