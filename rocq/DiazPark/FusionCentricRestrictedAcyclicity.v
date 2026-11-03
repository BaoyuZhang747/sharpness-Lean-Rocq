(** The full restricted-Mackey centric acyclicity theorem, from its
    inclusion-only formula. No ambient Mackey extension is required. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryFinite CategoryDerivedLimits
  FusionSystems FusionOrbit FusionSaturation FusionFiniteCategory
  FusionCentricProducts FusionCentricPullbacks FusionCentricHomCount
  FusionCentricAcyclicity FusionCentricRestrictedMackey MackeyPair MackeyPairDiagrams
  PrimeLocalRing BurnsideDerivedAcyclicity.
Import GRing.Theory DPPrimeLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionCentricRestrictedAcyclicity.
Theorem restricted_centric_higher_limits_zero (S : finGroupType)
    (F : DPFusionSystem.system S) (p : nat) (hp : prime p)
    (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (M : mackey_pair R (DPFusionOrbit.centric_orbit_category F))
    (hM : DPFusionCentricRestricted.inclusion_mackey_formula M) n :
    forall q : derived_limit R (pair_codiagram M) n.+1, q=0.
Proof.
pose Top := @DPFusionCentricAcyclicity.top_object S F.
apply: (@centric_mackey_positive_derived_zero S F Top
  (DPFusionCentricProducts.centric_product pS sat Top)
  (@DPFusionCentricPullbacks.centric_pullback S F)
  p hp _ R phi M (@DPFusionCentricRestricted.pullback_mackey_formula S F R M hM) n).
move=> X.
have h := @DPFusionCentricHomCount.top_hom_coprime S F p hp pS sat (val X) (valP X).
rewrite cardsT in h; exact h.
Qed.
End DPFusionCentricRestrictedAcyclicity.

Print Assumptions DPFusionCentricRestrictedAcyclicity.restricted_centric_higher_limits_zero.
