From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOuterOrbit
  MackeyPair FusionQuotientMaps FusionQuotientConstruction FusionQuotientAutomorphisms
  FusionQuotientOrbitMaps FusionQuotientOrbitLift FusionMackeyQuotientIndependence.
Import DPFusionOrbit DPFusionOuterOrbit DPFusionQuotientConstruction
  DPFusionQuotientAutomorphisms DPFusionQuotientOrbitMaps DPFusionQuotientOrbitLift
  DPFusionMackeyQuotientIndependence.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionMackeyQuotientPair.
Section Pair.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Hypothesis kernel_trivial : forall (P : {group coset_of Z}) a,
  a \in 'ker (automorphism_morphism cZ P) ->
  forall x : pair_value M (preimage P), pair_push M (aut_orbit F (preimage P) a) x = x.

Definition quotient_pull (P Q : {group coset_of Z}) (f : orbit_hom (system cZ) P Q) :
    {linear pair_value M (preimage Q) -> pair_value M (preimage P)} :=
  pair_pull M (lift_orbit f).
Definition quotient_push (P Q : {group coset_of Z}) (f : orbit_hom (system cZ) P Q) :
    {linear pair_value M (preimage P) -> pair_value M (preimage Q)} :=
  pair_push M (lift_orbit f).

Lemma quotient_push_induced (P Q : {group coset_of Z})
    (f : orbit_hom F (preimage P) (preimage Q)) x :
  quotient_push (orbit_map cZ f) x = pair_push M f x.
Proof.
have h := @orbit_map_coefficients S F Z cZ R M kernel_trivial P Q f
  (lift_orbit (orbit_map cZ f)) (esym (orbit_map_lift (orbit_map cZ f))).
exact: h.1.
Qed.

Lemma quotient_pull_induced (P Q : {group coset_of Z})
    (f : orbit_hom F (preimage P) (preimage Q)) x :
  quotient_pull (orbit_map cZ f) x = pair_pull M f x.
Proof.
have h := @orbit_map_coefficients S F Z cZ R M kernel_trivial P Q f
  (lift_orbit (orbit_map cZ f)) (esym (orbit_map_lift (orbit_map cZ f))).
exact: h.2.
Qed.

Lemma quotient_pull_identity (P : {group coset_of Z}) x :
  quotient_pull (orbit_identity (system cZ) P) x = x.
Proof. by rewrite -orbit_map_identity quotient_pull_induced pair_pull_id. Qed.
Lemma quotient_push_identity (P : {group coset_of Z}) x :
  quotient_push (orbit_identity (system cZ) P) x = x.
Proof. by rewrite -orbit_map_identity quotient_push_induced pair_push_id. Qed.

Lemma quotient_pull_compose (P Q T : {group coset_of Z})
    (f : orbit_hom (system cZ) P Q) (g : orbit_hom (system cZ) Q T) x :
  quotient_pull (orbit_compose f g) x = quotient_pull f (quotient_pull g x).
Proof.
have h : orbit_map cZ (orbit_compose (lift_orbit f) (lift_orbit g)) = orbit_compose f g.
  by rewrite orbit_map_compose !orbit_map_lift.
rewrite -h quotient_pull_induced pair_pull_comp.
reflexivity.
Qed.
Lemma quotient_push_compose (P Q T : {group coset_of Z})
    (f : orbit_hom (system cZ) P Q) (g : orbit_hom (system cZ) Q T) x :
  quotient_push (orbit_compose f g) x = quotient_push g (quotient_push f x).
Proof.
have h : orbit_map cZ (orbit_compose (lift_orbit f) (lift_orbit g)) = orbit_compose f g.
  by rewrite orbit_map_compose !orbit_map_lift.
rewrite -h quotient_push_induced pair_push_comp.
reflexivity.
Qed.

Lemma quotient_pull_isomorphism (P Q : {group coset_of Z})
    (e : @isomorphism (orbit_category (system cZ)) P Q) x :
  quotient_pull (iso_hom e) x = quotient_push (iso_inv e) x.
Proof.
rewrite /quotient_pull -(lift_isomorphism_hom e) pair_pull_iso.
have h := quotient_push_induced (iso_inv (lift_isomorphism e)) x.
by rewrite orbit_map_lift_isomorphism_inv in h.
Qed.

Definition quotient_pair : mackey_pair R (orbit_category (system cZ)) :=
  @MackeyPair R (orbit_category (system cZ))
    (fun P => pair_value M (preimage P)) quotient_pull quotient_push
    quotient_pull_identity quotient_push_identity quotient_pull_compose
    quotient_push_compose quotient_pull_isomorphism.

Theorem quotient_pair_value (P : {group coset_of Z}) :
  pair_value quotient_pair P = pair_value M (preimage P).
Proof. reflexivity. Qed.

Theorem quotient_pair_push (P Q : {group coset_of Z})
    (f : orbit_hom F (preimage P) (preimage Q)) x :
  pair_push quotient_pair (orbit_map cZ f) x = pair_push M f x.
Proof. exact: quotient_push_induced. Qed.

Theorem quotient_pair_pull (P Q : {group coset_of Z})
    (f : orbit_hom F (preimage P) (preimage Q)) x :
  pair_pull quotient_pair (orbit_map cZ f) x = pair_pull M f x.
Proof. exact: quotient_pull_induced. Qed.
End Pair.
End DPFusionMackeyQuotientPair.
