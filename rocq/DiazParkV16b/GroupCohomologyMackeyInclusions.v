(** The literal fusion inclusion push is the native subgroup transfer. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules FusionMaps FusionSystems FusionMackeyShape.
From DiazParkV16b Require Import GroupCohomologyFunctor GroupCohomologyPullback
  GroupCohomologyTransferNative GroupCohomologyTransferCovarianceSquare
  GroupCohomologyMackeyPushBase GroupCohomologyOrbitCoefficient LinkingCommaNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyTransferNative DPGroupCohomologyTransferCovarianceSquare
  DPGroupCohomologyMackeyPushBase DPGroupCohomologyOrbitCoefficient DPLinkingCommaNaturality.

Local Open Scope group_scope.

Module DPGroupCohomologyMackeyInclusions.
Section Inclusion.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q : {group S}.
Variable h : P \subset Q.
Local Notation a := (DPFusionMackey.inclusion_arrow F h).
Local Notation I := (DPFusion.image (val a)).

Lemma inclusion_image : I = P.
Proof.
apply val_inj; apply/setP => x; apply/idP/idP.
- move=> /morphimP[y Py _ ->].
  by rewrite map_morphismE inclusion_in.
- move=> Px; have hs := image_mem (inclusion h) Px.
  by rewrite inclusion_in // in hs.
Qed.

Lemma inclusion_inverse_value (x : [subg I]) :
  val (arrow_group_hom (DPFusionMackey.inverse_arrow a) x) = val x.
Proof.
have hs := @inverse_cancel_right S P Q (val a) (val x) (valP x).
have hy := map_into (inverse (val a)) (valP x).
change (inclusion h (inverse (val a) (val x)) = val x) in hs.
by rewrite inclusion_in // in hs.
Qed.

Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Theorem raw_push_inclusion : raw_push A n a = transfer A h n.
Proof.
pose e := [morphism of idm Q].
have hI : (e @* I)%G = P.
  apply val_inj; change (idm Q @* I = (P : {set S})).
  rewrite morphim_idm ?image_sub //; exact (congr1 val inclusion_image).
have hQ : (e @* Q)%G = Q.
  apply val_inj; exact: im_idm.
have hs := @transfer_covariance_named R S S I Q (image_sub (val a)) e (injm_idm Q)
  P Q h (arrow_group_hom (DPFusionMackey.inverse_arrow a))
  (group_hom_identity [the finGroupType of [subg Q]%type]) hI hQ
  inclusion_inverse_value (fun x => Logic.eq_refl (val x)) A n.
change (raw_push A n a = module_hom_comp (transfer A h n)
  (pull A (group_hom_identity [the finGroupType of [subg Q]%type]) n)) in hs.
rewrite pull_identity in hs; rewrite hs; apply module_hom_ext => z; reflexivity.
Qed.

End Inclusion.
End DPGroupCohomologyMackeyInclusions.


