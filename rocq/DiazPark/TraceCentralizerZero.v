From mathcomp Require Import all_boot all_algebra all_fingroup center pgroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape MackeyStructures MackeyPair MackeyFusionBridge
  TraceCharacteristic TraceCosets TraceNormalizerCosets TraceMackeySurvivors
  TraceNormalizerAction TraceMackeyQuotient TraceCentralizerIndex.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionMackey DPMackeyTrace DPNormalizerAction.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPCentralizerTrace.
Section CentralizerTriviality.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).
Variables H T : {group S}.

Lemma centralizer_product_quotient_trivial (q : coset_of H) :
    q \in (DPTraceCentralizer.product H T / H)%g ->
    forall v : pair_value M H, @quotient_action S F R M H v q = v.
Proof.
move=> /morphimP[d Nd dD ->] v.
have [h [Hh hd]] := DPTraceCentralizer.product_conjugation_inner dD.
have Nh : h \in 'N(H) := subsetP (normG H) h Hh.
have he : normalizer_arrow F Nd = normalizer_arrow F Nh.
  apply: DPFusionSystem.arrow_ext=> x Hx.
  rewrite !normalizer_arrow_value //; exact: hd Hx.
rewrite /quotient_action (quotient_class_coset F Nd) /normalizer_class he.
change (pair_push M (normalizer_class F Nh) v = v).
by rewrite (normalizer_class_inner F Hh Nh) pair_push_id.
Qed.

Variable p : nat.
Hypothesis charp : p%:R = (0 : R).
Hypothesis hHT : H \subset T.
Hypothesis pT : p.-group T.
Hypothesis noncentric : ~~ (T :&: 'C(H) \subset H).

Lemma quotient_trace_zero (x : pair_value M H) :
    \sum_(q in (trace_normalizer H T / H)%g) @quotient_action S F R M H x q = 0.
Proof.
have hsub : (DPTraceCentralizer.product H T / H)%g \subset (trace_normalizer H T / H)%g.
  exact: DPTraceCentralizer.quotient_sub_normalizer_quotient hHT.
have hmul : forall (v : pair_value M H) (a b : coset_of H),
    a \in (trace_normalizer H T / H)%g -> b \in (trace_normalizer H T / H)%g ->
    @quotient_action S F R M H (@quotient_action S F R M H v a) b =
      @quotient_action S F R M H v (a * b)%g.
  move=> v a b _ _; exact: quotient_action_mul.
have htriv : forall (v : pair_value M H) (q : coset_of H),
    q \in (DPTraceCentralizer.product H T / H)%g -> @quotient_action S F R M H v q = v.
  move=> v q hq; exact (@centralizer_product_quotient_trivial q hq v).
exact (@trace_trivial_subgroup_zero (coset_of H) _
  (trace_normalizer H T / H)%G (DPTraceCentralizer.product H T / H)%G
  hsub (@quotient_action S F R M H) hmul htriv p x
  (@trace_char_mul_zero R (pair_value M H) p charp)
  (DPTraceCentralizer.quotient_card_divisible hHT pT noncentric)).
Qed.

Hypothesis minimal : forall A : {group S}, (#|A| < #|H|)%N ->
  forall x : pair_value M A, x = 0.
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.

Theorem centralizer_self_transfer_zero (x : pair_value M H) :
    pair_pull M (DPFusionOrbit.orbit_class (inclusion_arrow F hHT))
      (pair_push M (DPFusionOrbit.orbit_class (inclusion_arrow F hHT)) x) = 0.
Proof.
rewrite (@self_trace_quotient S F R M H T minimal hHT hM x).
exact: quotient_trace_zero.
Qed.

End CentralizerTriviality.
End DPCentralizerTrace.

Print Assumptions DPCentralizerTrace.centralizer_product_quotient_trivial.
Print Assumptions DPCentralizerTrace.quotient_trace_zero.
Print Assumptions DPCentralizerTrace.centralizer_self_transfer_zero.
