(** Actual pushforward agrees with inverse pullback on isomorphisms and
    every inner automorphism acts trivially. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules FusionMaps FusionSystems
  FusionOrbit FusionOrbitRanks.
From DiazParkV16b Require Import GroupCohomologyOrbitCoefficient GroupCohomologyMackeyPushBase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomologyOrbitCoefficient DPGroupCohomologyMackeyPushBase.
Local Open Scope ring_scope.

Module DPGroupCohomologyMackeyPushIso.
Section Isomorphism.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation V := (@DPGroupCohomologyOrbitCoefficient.value S R A n).

Theorem raw_push_inverse (P Q : {group S})
    (a : DPFusionSystem.arrow F P Q) (b : DPFusionSystem.arrow F Q P)
    (hab : DPFusionSystem.arrow_compose a b = DPFusionSystem.arrow_identity F P) :
  raw_push A n a = raw_pull A n b.
Proof.
have hcard : #|P| = #|Q|.
  apply/eqP; rewrite eqn_leq; apply/andP; split;
    [exact: DPFusionRanks.raw_rank_le a | exact: DPFusionRanks.raw_rank_le b].
have himage := DPFusionRanks.raw_equal_rank_image a hcard.
apply module_hom_ext => z.
have hs := congr1 (fun k => module_hom_fun k z)
  (@raw_pull_compose S F R A n P Q P a b).
rewrite hab raw_pull_identity in hs.
change (z = module_hom_fun (raw_pull A n a) (module_hom_fun (raw_pull A n b) z)) in hs.
rewrite {1}hs raw_push_pull_index himage indexgg mulr1n; reflexivity.
Qed.

Theorem raw_push_inner (P : {group S}) (a : DPFusionSystem.arrow F P P)
    (ha : DPFusionOrbit.target_inner (DPFusionSystem.arrow_identity F P) a) :
  raw_push A n a = module_hom_id (V P).
Proof.
have himage := DPFusionRanks.raw_equal_rank_image a (Logic.eq_refl #|P|).
have hp := @raw_pull_inner S F R A n P P (DPFusionSystem.arrow_identity F P) a ha.
rewrite raw_pull_identity in hp.
apply module_hom_ext => z.
have hs := @raw_push_pull_index S F R A n P P a z.
rewrite hp himage indexgg mulr1n in hs.
exact hs.
Qed.

End Isomorphism.
End DPGroupCohomologyMackeyPushIso.
