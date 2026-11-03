(** Each actual native transfer/conjugation term is the canonical fusion span. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape FusionMackeyRepresentatives MackeyPair MackeyPairSpanIso.
From DiazParkV16b Require Import GroupCohomologyFunctor GroupCohomologyPullback
  GroupCohomologyOrbitCoefficient GroupCohomologyHomogeneousConjugation
  GroupCohomologyTransferNative GroupCohomologyTransferDoubleCoset GroupCohomologyMackeyPushBase
  GroupCohomologyMackeyPair GroupCohomologyMackeyInclusions LinkingCommaNaturality
  GroupCohomologyMackeyDoubleCosetGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyOrbitCoefficient DPGroupCohomologyHomogeneousConjugation
  DPGroupCohomologyTransferNative DPGroupCohomologyTransferDoubleCoset DPGroupCohomologyMackeyPushBase
  DPGroupCohomologyMackeyPair DPGroupCohomologyMackeyInclusions DPLinkingCommaNaturality
  DPGroupCohomologyMackeyDoubleCosetGeometry.
Local Open Scope group_scope.

Module DPGroupCohomologyMackeyDoubleCosetTerms.
Section Terms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Variables P Q : {group S}.
Local Notation M := (native_cohomology_pair F A n).

Lemma native_left_group_hom t :
  arrow_group_hom (native_left F P Q t) =
    @subgroup_conjugation_hom S (intersection P Q t) P t (intersection_sub_conjugate P Q t).
Proof.
apply group_morphism_ext=> x; apply val_inj.
rewrite subgroup_conjugation_hom_val.
exact: DPFusion.conjugation_in (valP x).
Qed.

Theorem canonical_summand_native t (z : pair_value M P) :
  @DPMackeyRepresentatives.inclusion_summand S F R M P Q t z =
    module_hom_fun (transfer A (intersection_sub_Q P Q t) n)
      (module_hom_fun
        (pull A (@subgroup_conjugation_hom S (intersection P Q t) P t
          (intersection_sub_conjugate P Q t)) n) z).
Proof.
have h := @pair_span_iso_invariance R (DPFusionOrbit.orbit_category F) M
  (native_apex P Q t) (DPFusionMackey.inclusion_apex P Q t) P Q
  (apex_iso F P Q t)
  (DPFusionOrbit.orbit_class (native_left F P Q t))
  (DPFusionOrbit.orbit_class (native_right F P Q t))
  (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_left F P Q t))
  (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_right F P Q t))
  (apex_iso_left F P Q t) (apex_iso_right F P Q t) z.
rewrite native_pair_push_class native_pair_pull_class /native_right raw_push_inclusion in h.
rewrite /raw_pull native_left_group_hom in h.
exact: esym h.
Qed.

End Terms.
End DPGroupCohomologyMackeyDoubleCosetTerms.
