From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category ModuleInfrastructure MackeyModuleCarriers
  FusionMaps FusionSystems FusionConjugacy FusionOrbit FusionMackeyShape
  MackeyStructures MackeyPair MackeyFusionBridge TraceCrossTransfer.
From DiazParkV29 Require Import SimpleTraceSummands.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPFusionMackey DPSimpleTraceSummands.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPSimpleTraceRestriction.
Section CrossTerms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Variable hM : DPMackeyFusion.inclusion_mackey_formula M.
Variables L K U : {group S}.
Variable hLU : L \subset U.
Variable hKU : K \subset U.
Hypothesis minimal : forall A : {group S}, (#|A| < #|L|)%N ->
  forall x : pair_value M A, x = 0.
Hypothesis same_order : #|K| = #|L|.

Lemma nonconjugate_cross_restriction
    (nonconjugate : ~~ [exists t in U, K :^ t == L]) (x : pair_value M K) :
    pair_pull M (orbit_class (inclusion_arrow F hLU))
      (pair_push M (orbit_class (inclusion_arrow F hKU)) x) = 0.
Proof.
rewrite (hM hKU hLU); apply: big1=> i _.
pose t := double_coset_representative i.
have tU : t \in U := double_coset_representative_mem i.
have hn : K :^ t != L.
  apply/negP=> he; move/negP: nonconjugate=> hn; apply: hn.
  apply/exists_inP; by exists t.
have hs := DPTraceCrossTransfer.equal_order_intersection_small same_order hn.
have hz := @minimal (inclusion_apex K L t) hs
  (pair_pull M (span_left (inclusion_term F i)) x).
by rewrite hz linear0.
Qed.

Lemma cross_restriction_in_trace_image (x : pair_value M K) :
    trace_image M L U
      (pair_pull M (orbit_class (inclusion_arrow F hLU))
        (pair_push M (orbit_class (inclusion_arrow F hKU)) x)).
Proof.
case hc : [exists t in U, K :^ t == L].
- have /exists_inP[t tU /eqP ht] := hc.
  have hsub : K :^ t \subset L by rewrite ht.
  rewrite (@DPTraceCrossTransfer.inclusion_conjugation_factorization
    S F L K U hLU hKU t tU hsub) pair_push_comp.
  exists (pair_push M (orbit_class (DPTraceCrossTransfer.conjugation_arrow F hsub)) x).
  symmetry; exact (@self_restriction_is_trace S F R M L U hLU minimal hM _).
- rewrite (nonconjugate_cross_restriction _ x); first exact: subspace_zero.
  by rewrite hc.
Qed.
End CrossTerms.
End DPSimpleTraceRestriction.
