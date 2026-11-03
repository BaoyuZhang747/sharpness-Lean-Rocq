(** Actual pushforward along a fusion injection: inverse image-isomorphism
    pullback followed by the constructed native image-subgroup transfer. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  FusionMaps FusionSystems FusionOrbit FusionConjugacy FusionMackeyShape.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyPullback
  GroupCohomologyHomogeneousRestriction GroupCohomologyTransferNative
  GroupCohomologyTransferIndex GroupCohomologyOrbitCoefficient LinkingCommaNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomologyPullback DPGroupCohomologyHomogeneousRestriction
  DPGroupCohomologyTransferNative DPGroupCohomologyTransferIndex
  DPGroupCohomologyOrbitCoefficient DPLinkingCommaNaturality.
Local Open Scope ring_scope.

Module DPGroupCohomologyMackeyPushBase.
Section Push.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation V := (@DPGroupCohomologyOrbitCoefficient.value S R A n).
Local Notation rp := (@raw_pull S F R A n).

Lemma image_inverse_arrow (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) :
  DPFusionSystem.arrow_compose (DPFusionMackey.image_arrow a)
    (DPFusionMackey.inverse_arrow a) = DPFusionSystem.arrow_identity F P.
Proof. apply val_inj; exact: DPFusion.to_image_inverse. Qed.

Lemma inverse_image_arrow (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) :
  DPFusionSystem.arrow_compose (DPFusionMackey.inverse_arrow a)
    (DPFusionMackey.image_arrow a) =
      DPFusionSystem.arrow_identity F (DPFusion.image (val a)).
Proof. apply val_inj; exact: DPFusion.inverse_to_image. Qed.

Lemma image_inclusion_arrow (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) :
  DPFusionSystem.arrow_compose (DPFusionMackey.image_arrow a)
    (DPFusionMackey.inclusion_arrow F (DPFusion.image_sub (val a))) = a.
Proof. apply val_inj; exact: DPFusion.image_factorization. Qed.

Definition image_cohomology_iso (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) :
    @isomorphism (module_category R) (V P) (V (DPFusion.image (val a))).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (rp (DPFusionMackey.inverse_arrow a))
  (rp (DPFusionMackey.image_arrow a)) _ _).
- change (module_hom_comp (rp (DPFusionMackey.inverse_arrow a))
    (rp (DPFusionMackey.image_arrow a)) = module_hom_id (V P)).
  rewrite -raw_pull_compose image_inverse_arrow; exact: raw_pull_identity.
- change (module_hom_comp (rp (DPFusionMackey.image_arrow a))
    (rp (DPFusionMackey.inverse_arrow a)) = module_hom_id (V (DPFusion.image (val a)))).
  rewrite -raw_pull_compose inverse_image_arrow; exact: raw_pull_identity.
Defined.

Definition raw_push (P Q : {group S}) (a : DPFusionSystem.arrow F P Q) :
    module_hom (V P) (V Q) :=
  module_hom_comp (iso_hom (image_cohomology_iso a))
    (transfer A (DPFusion.image_sub (val a)) n).

Lemma raw_pull_inclusion (P Q : {group S}) (h : P \subset Q) :
  rp (DPFusionMackey.inclusion_arrow F h) = pull A (subgroup_nested_hom h) n.
Proof.
rewrite /raw_pull; congr (pull A _ n).
apply group_morphism_ext => x; apply val_inj.
rewrite subgroup_nested_hom_val.
exact: DPFusion.inclusion_in (valP x).
Qed.

Lemma raw_push_image_pull (P Q : {group S}) (a : DPFusionSystem.arrow F P Q)
    (z : V (DPFusion.image (val a))) :
  module_hom_fun (raw_push a) (module_hom_fun (rp (DPFusionMackey.image_arrow a)) z) =
    module_hom_fun (transfer A (DPFusion.image_sub (val a)) n) z.
Proof.
change (module_hom_fun (transfer A (DPFusion.image_sub (val a)) n)
    (module_hom_fun (iso_hom (image_cohomology_iso a))
      (module_hom_fun (iso_inv (image_cohomology_iso a)) z)) =
  module_hom_fun (transfer A (DPFusion.image_sub (val a)) n) z).
by rewrite module_iso_inv_hom_apply.
Qed.

Theorem raw_push_pull_index (P Q : {group S}) (a : DPFusionSystem.arrow F P Q)
    (z : V Q) :
  module_hom_fun (raw_push a) (module_hom_fun (rp a) z) =
    z *+ (indexg Q (DPFusion.image (val a))).
Proof.
have hf := @raw_pull_compose S F R A n P (DPFusion.image (val a)) Q
  (DPFusionMackey.image_arrow a)
  (DPFusionMackey.inclusion_arrow F (DPFusion.image_sub (val a))).
rewrite image_inclusion_arrow raw_pull_inclusion in hf.
rewrite hf.
change (module_hom_fun (raw_push a)
    (module_hom_fun (rp (DPFusionMackey.image_arrow a))
      (module_hom_fun (pull A (subgroup_nested_hom (DPFusion.image_sub (val a))) n) z)) =
  z *+ (indexg Q (DPFusion.image (val a)))).
rewrite raw_push_image_pull; exact: transfer_restriction_index.
Qed.

Lemma raw_push_identity (P : {group S}) :
  raw_push (DPFusionSystem.arrow_identity F P) = module_hom_id (V P).
Proof.
apply module_hom_ext => z.
have h := raw_push_pull_index (DPFusionSystem.arrow_identity F P) z.
rewrite raw_pull_identity in h.
change (module_hom_fun (raw_push (DPFusionSystem.arrow_identity F P)) z =
  z *+ indexg P (DPFusion.image (DPFusion.identity P))) in h.
by rewrite DPFusionConjugacy.identity_image indexgg mulr1n in h.
Qed.

End Push.
End DPGroupCohomologyMackeyPushBase.

