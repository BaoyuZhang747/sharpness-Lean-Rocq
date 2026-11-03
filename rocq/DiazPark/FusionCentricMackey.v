From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape MackeyStructures MackeyPair MackeyFusionBridge.
Import GRing.Theory DPFusionSystem DPFusionOrbit DPFusionMackey DPMackeyFusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricMackey.
Section SupportedCoefficients.
Variable S : finGroupType.
Variable F : system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Hypothesis hM : inclusion_mackey_formula M.
Hypothesis supported : forall P : {group S}, ~~ centric F P -> forall x : pair_value M P, x=0.

Theorem raw_centric_mackey_formula (P Q T : {group S})
    (f : arrow F P T) (g : arrow F Q T) (x : pair_value M P) :
    pair_pull M (orbit_class g) (pair_push M (orbit_class f) x) =
      \sum_(i : {i : raw_index f g | centric F (raw_apex f g (double_coset_representative i))})
        pair_push M (span_right (@raw_term S F P Q T f g (val i)))
          (pair_pull M (span_left (@raw_term S F P Q T f g (val i))) x).
Proof.
rewrite (raw_mackey_formula hM f g).
transitivity (\sum_(i : raw_index f g |
  centric F (raw_apex f g (double_coset_representative i)))
    pair_push M (span_right (@raw_term S F P Q T f g i))
      (pair_pull M (span_left (@raw_term S F P Q T f g i)) x)); last exact: big_sub.
rewrite [RHS]big_mkcond.
apply: eq_bigr=> i _.
case hc : (centric F (raw_apex f g (double_coset_representative i)))=> //.
have hz := supported (negbT hc)
  (pair_pull M (span_left (@raw_term S F P Q T f g i)) x).
by rewrite hz linear0.
Qed.
End SupportedCoefficients.
End DPFusionCentricMackey.

Print Assumptions DPFusionCentricMackey.raw_centric_mackey_formula.


