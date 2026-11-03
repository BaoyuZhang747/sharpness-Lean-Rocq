From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOrbitRanks
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientOrbitMaps.
Import DPFusionOrbit DPFusionQuotientConstruction DPFusionQuotientOrbitMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientOrbitLift.
Section Lifts.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

Lemma lift_exists (P Q : {group coset_of Z}) (f : orbit_hom (system cZ) P Q) :
  exists g : orbit_hom F (preimage P) (preimage Q), orbit_map cZ g == f.
Proof.
have [g hg] := orbit_map_surjective f.
by exists g; apply/eqP.
Qed.

Definition lift_orbit (P Q : {group coset_of Z}) (f : orbit_hom (system cZ) P Q) :
    orbit_hom F (preimage P) (preimage Q) := xchoose (lift_exists f).

Lemma orbit_map_lift (P Q : {group coset_of Z}) (f : orbit_hom (system cZ) P Q) :
  orbit_map cZ (lift_orbit f) = f.
Proof. exact: (eqP (xchooseP (lift_exists f))). Qed.

Lemma isomorphism_preimage_card (P Q : {group coset_of Z})
    (e : @isomorphism (orbit_category (system cZ)) P Q) :
  #|preimage P| = #|preimage Q|.
Proof.
have hcard : #|P| = #|Q|.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - exact: DPFusionRanks.orbit_rank_le (iso_hom e).
  - exact: DPFusionRanks.orbit_rank_le (iso_inv e).
by rewrite /preimage !card_cosetpre hcard.
Qed.

Definition lift_isomorphism (P Q : {group coset_of Z})
    (e : @isomorphism (orbit_category (system cZ)) P Q) :
    @isomorphism (orbit_category F) (preimage P) (preimage Q) :=
  DPFusionRanks.orbit_equal_rank_iso (lift_orbit (iso_hom e)) (isomorphism_preimage_card e).

Lemma lift_isomorphism_hom (P Q : {group coset_of Z})
    (e : @isomorphism (orbit_category (system cZ)) P Q) :
  iso_hom (lift_isomorphism e) = lift_orbit (iso_hom e).
Proof. exact: DPFusionRanks.orbit_equal_rank_iso_hom. Qed.

Lemma orbit_map_lift_isomorphism_inv (P Q : {group coset_of Z})
    (e : @isomorphism (orbit_category (system cZ)) P Q) :
  orbit_map cZ (iso_inv (lift_isomorphism e)) = iso_inv e.
Proof.
have h := congr1 (@orbit_map S F Z cZ P P) (iso_hom_inv (lift_isomorphism e)).
change (orbit_map cZ (orbit_compose (iso_hom (lift_isomorphism e))
  (iso_inv (lift_isomorphism e))) = orbit_map cZ (orbit_identity F (preimage P))) in h.
rewrite orbit_map_compose lift_isomorphism_hom orbit_map_lift orbit_map_identity in h.
change (compose (iso_hom e) (orbit_map cZ (iso_inv (lift_isomorphism e))) =
  @identity (orbit_category (system cZ)) P) in h.
rewrite -(@compose_id_left (orbit_category (system cZ)) Q P
  (orbit_map cZ (iso_inv (lift_isomorphism e)))).
rewrite -(iso_inv_hom e) compose_assoc h.
exact: (@compose_id_right (orbit_category (system cZ)) Q P (iso_inv e)).
Qed.
End Lifts.
End DPFusionQuotientOrbitLift.
