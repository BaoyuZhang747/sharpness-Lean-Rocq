From mathcomp Require Import all_boot all_algebra all_fingroup center pgroup.
From DiazPark Require Import Category ModuleInfrastructure FusionMaps FusionSystems
  FusionOrbit FusionConjugacy FusionMackeyShape MackeyStructures MackeyPair
  MackeyFusionBridge MackeyFusionMinimal TraceCentralizerZero TraceCrossTransfer.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionMackey DPMackeyFusion DPMackeyMinimal.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPCentralizerRestriction.
Section RestrictionZero.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).
Hypothesis hM : inclusion_mackey_formula M.
Let full := full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Variables H T : {group S}.
Hypothesis hQH : DPFusionSystem.conjugate F Q H.
Hypothesis hHT : H \subset T.
Variable p : nat.
Hypothesis charp : p%:R = (0 : R).
Hypothesis pT : p.-group T.
Hypothesis noncentric : ~~ (T :&: 'C(H) \subset H).

Lemma conjugate_smaller_vanish (A : {group S}) : (#|A| < #|H|)%N ->
    forall x : pair_value M A, x = 0.
Proof.
move=> ha x; apply: leastQ.2.
by rewrite (DPFusionConjugacy.conjugate_card hQH).
Qed.

(** This is the actual restriction map, not merely its composite with its
    own transfer. Every inclusion-transfer generator is killed by the proved
    cross-transfer calculation, and linearity kills its entire span. *)
Theorem centralizer_restriction_zero (x : pair_value M T) :
    pair_pull M (DPFusionOrbit.orbit_class (inclusion_arrow F hHT)) x = 0.
Proof.
have self_zero : forall v : pair_value M H,
    pair_pull M (DPFusionOrbit.orbit_class (inclusion_arrow F hHT))
      (pair_push M (DPFusionOrbit.orbit_class (inclusion_arrow F hHT)) v) = 0.
  exact (@DPCentralizerTrace.centralizer_self_transfer_zero S F R M H T p
    charp hHT pT noncentric (@conjugate_smaller_vanish) hM).
have hg := @DPMackeyMinimal.inclusion_transfer_generation S F R full Q leastQ simple T x.
elim: hg => [v [K [hKT [hQK [w <-]]]] | |v w hv ihv hw ihw |a v hv ihv].
- have hc : #|K| = #|H|.
    by rewrite -(DPFusionConjugacy.conjugate_card hQK)
      (DPFusionConjugacy.conjugate_card hQH).
  exact (@DPTraceCrossTransfer.cross_transfer_zero S F R M H
    (@conjugate_smaller_vanish) hM K T hHT hKT hc self_zero w).
- exact: linear0.
- by rewrite linearD ihv ihw addr0.
- by rewrite linearZ /= ihv scaler0.
Qed.

End RestrictionZero.
End DPCentralizerRestriction.

Print Assumptions DPCentralizerRestriction.centralizer_restriction_zero.
