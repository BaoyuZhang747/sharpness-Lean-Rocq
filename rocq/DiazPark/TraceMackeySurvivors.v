From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape FusionOrbitRanks MackeyStructures MackeyPair MackeyFusionBridge
  TraceNormalizerCosets.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionMackey DPFusionRanks.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPMackeyTrace.
Section NormalizerArrows.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable H : {group S}.

Lemma normalizer_conjugation_range t (ht : t \in 'N(H)) : H :^ t \subset H.
Proof. by rewrite (normP ht). Qed.

Definition normalizer_arrow t (ht : t \in 'N(H)) : DPFusionSystem.arrow F H H :=
  Sub (DPFusion.conjugation (normalizer_conjugation_range ht))
    (DPFusionSystem.conjugation_closed F (normalizer_conjugation_range ht)).

Lemma normalizer_arrow_value t (ht : t \in 'N(H)) x : x \in H ->
    DPFusion.map_fun (val (normalizer_arrow ht)) x = (x ^ t)%g.
Proof. exact: DPFusion.conjugation_in. Qed.

Lemma normalizing_right_leg t (ht : t \in 'N(H)) :
    span_right (inclusion_span F H H t) =
    Category.compose (span_left (inclusion_span F H H t))
      (DPFusionOrbit.orbit_class (normalizer_arrow ht)).
Proof.
cbn [Category.compose DPFusionOrbit.orbit_category span_left span_right inclusion_span].
rewrite DPFusionOrbit.orbit_compose_class.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Ax.
rewrite /DPFusionSystem.arrow_compose /inclusion_left /inclusion_right /normalizer_arrow /=.
rewrite DPFusion.compose_in // !DPFusion.conjugation_in // DPFusion.inclusion_in //.
exact: (subsetP (inclusion_apex_left H H t) x Ax).
Qed.

End NormalizerArrows.

Section SelfTrace.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).
Variable H : {group S}.
Hypothesis minimal : forall A : {group S}, (#|A| < #|H|)%N ->
  forall x : pair_value M A, x = 0.

Definition self_term t (x : pair_value M H) :=
  pair_push M (span_right (inclusion_span F H H t))
    (pair_pull M (span_left (inclusion_span F H H t)) x).

Lemma self_term_nonnormalizer t (ht : t \notin 'N(H)) (x : pair_value M H) :
    self_term t x = 0.
Proof.
have hz := @minimal (inclusion_apex H H t) (trace_self_apex_card_lt ht)
  (pair_pull M (span_left (inclusion_span F H H t)) x).
by rewrite /self_term hz linear0.
Qed.

Lemma self_term_normalizer t (ht : t \in 'N(H)) (x : pair_value M H) :
    self_term t x = pair_push M (DPFusionOrbit.orbit_class (normalizer_arrow F ht)) x.
Proof.
have ha : inclusion_apex H H t = H by apply/eqP; rewrite trace_self_apex_normalizer.
have hc : #|inclusion_apex H H t| = #|H| by rewrite ha.
pose e := orbit_equal_rank_iso (span_left (inclusion_span F H H t)) hc.
have he := orbit_equal_rank_iso_hom (span_left (inclusion_span F H H t)) hc.
rewrite /self_term (normalizing_right_leg F ht) pair_push_comp -he pair_pull_iso.
apply: congr1.
rewrite -pair_push_comp iso_inv_hom pair_push_id.
reflexivity.
Qed.

Variable T : {group S}.
Hypothesis hHT : H \subset T.
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.

Theorem self_trace_survivors (x : pair_value M H) :
    pair_pull M (DPFusionOrbit.orbit_class (inclusion_arrow F hHT))
      (pair_push M (DPFusionOrbit.orbit_class (inclusion_arrow F hHT)) x) =
    \sum_(i : trace_survivor H T)
      pair_push M (DPFusionOrbit.orbit_class
        (normalizer_arrow F (valP i))) x.
Proof.
rewrite (hM hHT hHT).
transitivity (\sum_(i : double_coset_index H H T |
  double_coset_representative i \in 'N(H)) self_term (double_coset_representative i) x).
- rewrite [RHS]big_mkcond; apply: eq_bigr=> i _.
  case hn : (double_coset_representative i \in 'N(H)); first reflexivity.
  apply: self_term_nonnormalizer; by rewrite hn.
- rewrite big_sub; apply: eq_bigr=> i _.
  exact: self_term_normalizer.
Qed.

End SelfTrace.
End DPMackeyTrace.

Print Assumptions DPMackeyTrace.self_term_normalizer.
Print Assumptions DPMackeyTrace.self_trace_survivors.
