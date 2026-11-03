(** Concrete support and orbit facts needed to prove the atomic Kan unit. *)
From mathcomp Require Import all_boot all_fingroup pgroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOrbitRanks
  FusionOuterCard FusionOuterAction FusionAtomicFunctorPreimages FusionAtomicFunctorFixed
  FusionAtomicFunctorStabilizer GroupActionOrbitRepresentatives.
Import DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionAtomicGeometry.
Section Geometry.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation OC := (orbit_category F).

Lemma orbit_iso_card (Q P : {group S}) (e : @isomorphism OC Q P) : #|Q| = #|P|.
Proof. apply/eqP. rewrite eqn_leq. apply/andP; split;
  [exact (DPFusionRanks.orbit_rank_le (iso_hom e)) | exact (DPFusionRanks.orbit_rank_le (iso_inv e))]. Qed.

Variable Q : {group S}.
Local Notation G := (DPFusionAtomicPreimages.outer_type F Q).
Local Notation T := (DPFusionAtomicPreimages.ambient_outer F Q).
Local Notation QH H := (@DPFusionAtomicPreimages.preimage S F Q H).

Lemma native_action_transitive (P : {group S}) (e : @isomorphism OC Q P)
    (x y : orbit_hom F Q P) :
    exists g : G, DPFusionAtomicNativeStabilizer.action g y = x.
Proof.
  pose ey := DPFusionRanks.orbit_equal_rank_iso y (orbit_iso_card e).
  have [a [ha hea]] := DPFusionOuterCard.outer_orbit_surjective (orbit_compose x (iso_inv ey)).
  exists (Sub a ha).
  change (orbit_compose (DPFusionOuterAction.outer_orbit F a) y = x).
  rewrite hea -(DPFusionRanks.orbit_equal_rank_iso_hom y (orbit_iso_card e)).
  change (@compose OC Q Q P (@compose OC Q P Q x (iso_inv ey)) (iso_hom ey) = x).
  by rewrite compose_assoc iso_inv_hom compose_id_right.
Qed.

Definition hom_orbit_index (P : {group S}) := @DPLeftAction.orbit_index G
  [the finType of orbit_hom F Q P] (@DPFusionAtomicNativeStabilizer.action S F Q P)
  (@DPFusionAtomicNativeStabilizer.action_one S F Q P)
  (@DPFusionAtomicNativeStabilizer.action_mul S F Q P).

Lemma hom_orbit_index_singleton (P : {group S}) (e : @isomorphism OC Q P)
    (i j : hom_orbit_index P) : i = j.
Proof.
  rewrite -(reprK i) -(reprK j). apply/DPLeftAction.orbit_class_eq/existsP.
  have [g hg] := native_action_transitive e (repr i) (repr j).
  exists g. exact/eqP.
Qed.

Hypothesis centricQ : DPFusionSystem.centric F Q.

Lemma nontrivial_preimage_not_isomorphic (H : {group G}) (hHT : H \subset T)
    (ntH : H :!=: 1%G) (e : @isomorphism OC Q (QH H)) : False.
Proof.
  have hc := orbit_iso_card e.
  rewrite (DPFusionAtomicPreimages.preimage_card centricQ hHT) in hc.
  have h1 : #|H| = 1%N.
    apply/eqP. rewrite -(@eqn_pmul2l #|Q| #|H| 1 (cardG_gt0 Q)) muln1.
    exact/eqP; exact (esym hc).
  by move: ntH; rewrite trivg_card1 h1 eqxx.
Qed.

Definition preimage_arrow_iso (P : {group S}) (e : @isomorphism OC Q P)
    (H : {group G}) (b : orbit_hom F (QH H) P) : @isomorphism OC (QH H) P.
Proof.
  apply (DPFusionRanks.orbit_equal_rank_iso b).
  apply/eqP. rewrite eqn_leq. apply/andP; split; first exact (DPFusionRanks.orbit_rank_le b).
  rewrite -(orbit_iso_card e).
  exact (subset_leq_card (DPFusionAtomicPreimages.source_sub_preimage centricQ H)).
Defined.
Lemma preimage_arrow_iso_hom (P : {group S}) (e : @isomorphism OC Q P)
    (H : {group G}) (b : orbit_hom F (QH H) P) : iso_hom (preimage_arrow_iso e b) = b.
Proof. exact: DPFusionRanks.orbit_equal_rank_iso_hom. Qed.

End Geometry.
End DPFusionAtomicGeometry.
