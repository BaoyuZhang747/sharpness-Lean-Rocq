From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape MackeyStructures MackeyPair MackeyFusionBridge.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionMackey.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPTraceCrossTransfer.
Section Intersections.
Variable S : finGroupType.
Variables H K : {group S}.

Lemma equal_order_intersection_small t :
  #|K| = #|H| -> K :^ t != H ->
  (#|inclusion_apex K H t| < #|H|)%N.
Proof.
move=> hc hn.
have sAK := inclusion_apex_left K H t.
rewrite -hc ltn_neqAle (subset_leq_card sAK) andbT.
apply/negP=> /eqP hcard.
have hAK : inclusion_apex K H t = K :> {set S}.
  by apply/eqP; rewrite eqEcard sAK hcard leqnn.
have sKH : K \subset H :^ t^-1.
  rewrite -hAK; exact: subsetIr.
have hKH : K = H :^ t^-1 :> {set S}.
  by apply/eqP; rewrite eqEcard sKH cardJg -hc leqnn.
have hconj : K :^ t = H by rewrite hKH conjsgKV.
by move: hn; rewrite hconj eqxx.
Qed.

End Intersections.

Section OrbitTransport.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables H K T : {group S}.
Variables (hHT : H \subset T) (hKT : K \subset T).
Variable t : S.
Hypothesis tT : t \in T.
Hypothesis hconj : K :^ t \subset H.

Definition conjugation_arrow : DPFusionSystem.arrow F K H :=
  Sub (DPFusion.conjugation hconj) (DPFusionSystem.conjugation_closed F hconj).

Lemma inclusion_conjugation_factorization :
  orbit_class (inclusion_arrow F hKT) =
  @Category.compose (orbit_category F) K H T
    (orbit_class conjugation_arrow) (orbit_class (inclusion_arrow F hHT)).
Proof.
cbn [Category.compose orbit_category].
rewrite orbit_compose_class.
apply/orbit_class_eq/exists_inP; exists t=> //.
apply/forall_inP=> x xK; apply/eqP.
change (DPFusion.compose (val conjugation_arrow)
  (val (inclusion_arrow F hHT)) x = ((DPFusion.inclusion hKT x) ^ t)%g).
rewrite DPFusion.compose_in // DPFusion.inclusion_in //.
have cxH : DPFusion.map_fun (val conjugation_arrow) x \in H.
  exact: DPFusion.map_into xK.
rewrite DPFusion.inclusion_in //.
exact: DPFusion.conjugation_in.
Qed.

End OrbitTransport.

Section CrossTransfer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).
Variable H : {group S}.
Hypothesis minimal : forall A : {group S}, (#|A| < #|H|)%N ->
  forall x : pair_value M A, x = 0.
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.
Variables K T : {group S}.
Variables (hHT : H \subset T) (hKT : K \subset T).
Hypothesis hc : #|K| = #|H|.
Hypothesis self_zero : forall x : pair_value M H,
  pair_pull M (orbit_class (inclusion_arrow F hHT))
    (pair_push M (orbit_class (inclusion_arrow F hHT)) x) = 0.

Theorem cross_transfer_zero (x : pair_value M K) :
  pair_pull M (orbit_class (inclusion_arrow F hHT))
    (pair_push M (orbit_class (inclusion_arrow F hKT)) x) = 0.
Proof.
case hTK : [exists t in T, K :^ t == H].
- have /exists_inP[t tT /eqP ht] := hTK.
  have hsub : K :^ t \subset H by rewrite ht.
  rewrite (@inclusion_conjugation_factorization S F H K T hHT hKT t tT hsub).
  rewrite pair_push_comp; exact: self_zero.
- rewrite (hM hKT hHT); apply: big1=> i _.
  pose t := double_coset_representative i.
  have tT : t \in T := double_coset_representative_mem i.
  have hn : K :^ t != H.
    apply/negP=> he.
    have hex : [exists t in T, K :^ t == H].
      apply/exists_inP; by exists t.
    by move: hTK; rewrite hex.
  have hs := equal_order_intersection_small hc hn.
  have hz := @minimal (inclusion_apex K H t) hs
    (pair_pull M (span_left (inclusion_term F i)) x).
  by rewrite hz linear0.
Qed.

End CrossTransfer.
End DPTraceCrossTransfer.

Print Assumptions DPTraceCrossTransfer.equal_order_intersection_small.
Print Assumptions DPTraceCrossTransfer.inclusion_conjugation_factorization.
Print Assumptions DPTraceCrossTransfer.cross_transfer_zero.
