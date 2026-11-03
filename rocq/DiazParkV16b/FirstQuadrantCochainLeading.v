(** Leading-column cocycles and honest lifting through horizontal cohomology
    exactness. This is the algebraic input to finite-diagonal elimination. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import HomologicalComplex HomologicalMaps HomologicalCohomology
  HomologicalCohomologyMaps ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps FirstQuadrantCochainTotalSupport FirstQuadrantCochainEdge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology
  DiazParkCohomologyMaps DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps
  DPFirstQuadrantSupport DPFirstQuadrantEdge.
Local Open Scope ring_scope.

Module DPFirstQuadrantLeading.
Section Leading.
Variable R : pzRingType.
Variable K : bicomplex R.

Lemma sign_scale_cancel (V : lmodType R) p (x : V) :
    (-1 : R)^+p *: ((-1 : R)^+p *: x) = x.
Proof.
induction p as [|p IH].
- by rewrite expr0 !scale1r.
- by rewrite exprS mulN1r !scaleNr scalerN opprK IH.
Qed.

Lemma vertical_output_index p q n (h : (p + q)%coq_nat = n) :
    (p + q.+1)%coq_nat = n.+1.
Proof. by rewrite Nat.add_succ_r h. Qed.

Lemma horizontal_output_index p q n (h : (p + q)%coq_nat = n) :
    (p.+1 + q)%coq_nat = n.+1.
Proof. exact (f_equal S h). Qed.

Lemma leading_vertical_cycle n p q (hpq : (p + q)%coq_nat = n)
    (a : total_term K n) (ha : cocycle (total_complex K) n a)
    (hs : supported_from a p) :
    cocycle (vertical_complex K p) q (a p q hpq).
Proof.
have h := f_equal (fun v : total_term K n.+1 => v p q.+1 (vertical_output_index hpq)) ha.
destruct p as [|p].
- change (0 + (-1 : R)^+0 *: vertical K 0%N q
    (a 0%N q (vertical_index (vertical_output_index hpq))) = 0) in h.
  have he : vertical_index (vertical_output_index hpq) = hpq by apply Prop_irrelevance.
  by rewrite he expr0 scale1r add0r in h.
- change (horizontal K p q.+1 (a p q.+1 (horizontal_index (vertical_output_index hpq))) +
    (-1 : R)^+p.+1 *: vertical K p.+1 q
      (a p.+1 q (vertical_index (vertical_output_index hpq))) = 0) in h.
  have he : vertical_index (vertical_output_index hpq) = hpq by apply Prop_irrelevance.
  have hp : (p < p.+1)%coq_nat by lia.
  rewrite he (hs p q.+1 (horizontal_index (vertical_output_index hpq)) hp) linear0 add0r in h.
  have h' := f_equal (fun x : bicomplex_term K p.+1 q.+1 => (-1 : R)^+p.+1 *: x) h.
  rewrite sign_scale_cancel scaler0 in h'. exact h'.
Qed.

Lemma leading_horizontal_boundary n p q (hpq : (p + q)%coq_nat = n)
    (a : total_term K n) (ha : cocycle (total_complex K) n a) :
    coboundary (vertical_complex K p.+1) q (horizontal K p q (a p q hpq)).
Proof.
have h := f_equal (fun v : total_term K n.+1 => v p.+1 q (horizontal_output_index hpq)) ha.
destruct q as [|q].
- change (horizontal K p 0%N
    (a p 0%N (horizontal_index (horizontal_output_index hpq))) + 0 = 0) in h.
  have he : horizontal_index (horizontal_output_index hpq) = hpq by apply Prop_irrelevance.
  by rewrite he addr0 in h.
- change (horizontal K p q.+1
    (a p q.+1 (horizontal_index (horizontal_output_index hpq))) +
    (-1 : R)^+p.+1 *: vertical K p.+1 q
      (a p.+1 q (vertical_index (horizontal_output_index hpq))) = 0) in h.
  have he : horizontal_index (horizontal_output_index hpq) = hpq by apply Prop_irrelevance.
  rewrite he in h.
  exists (- ((-1 : R)^+p.+1 *: a p.+1 q (vertical_index (horizontal_output_index hpq)))).
  change (vertical K p.+1 q (- ((-1 : R)^+p.+1 *:
    a p.+1 q (vertical_index (horizontal_output_index hpq)))) = horizontal K p q.+1 (a p q.+1 hpq)).
  rewrite linearN linearZ.
  change (- ((-1 : R)^+p.+1 *: vertical K p.+1 q
    (a p.+1 q (vertical_index (horizontal_output_index hpq)))) = horizontal K p q.+1 (a p q.+1 hpq)).
  apply (addrI ((-1 : R)^+p.+1 *: vertical K p.+1 q
    (a p.+1 q (vertical_index (horizontal_output_index hpq))))).
  by rewrite subrr [RHS]addrC h.
Qed.

Lemma leading_horizontal_cycle n p q (hpq : (p + q)%coq_nat = n)
    (a : total_term K n) (ha : cocycle (total_complex K) n a)
    (hs : supported_from a p) :
    horizontal_cohomology K p q (cohomology_class (leading_vertical_cycle hpq ha hs)) = 0.
Proof.
rewrite /horizontal_cohomology cohomology_map_class.
apply/cohomology_class_zero.
exact: leading_horizontal_boundary.
Qed.

Lemma horizontal_cycle_lift (hK : positive_horizontal_exact K) p q
    (x : bicomplex_term K p.+1 q) (hx : cocycle (vertical_complex K p.+1) q x)
    (hh : horizontal_cohomology K p.+1 q (cohomology_class hx) = 0) :
    exists (a : bicomplex_term K p q) (ha : cocycle (vertical_complex K p) q a),
      coboundary (vertical_complex K p.+1) q (x - horizontal K p q a).
Proof.
have [y hy] := hK q p (cohomology_class hx) hh.
have [z hz] := quotient_pi_surjective y.
exists (cycle_inclusion (vertical_complex K p) q z), (submodule_val_mem z).
rewrite <- hz in hy.
rewrite /horizontal_cohomology cohomology_map_pi in hy.
apply (proj1 (@cohomology_pi_eq R (vertical_complex K p.+1) q
  (cycle_of_cocycle hx) (cycle_map (horizontal_column_map K p) q z))).
symmetry; exact hy.
Qed.
End Leading.
End DPFirstQuadrantLeading.
