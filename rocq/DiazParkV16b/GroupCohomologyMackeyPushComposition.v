(** Composition of actual fusion pushforwards follows from the native
    transfer square and subgroup tower, with literal image inverses. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp.
From DiazPark Require Import Category CategoryModules FusionMaps FusionSystems FusionMackeyShape.
From DiazParkV16b Require Import GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  GroupCohomologyTransferNative GroupCohomologyTransferTower
  GroupCohomologyTransferCovarianceSquare GroupCohomologyMackeyPushBase
  GroupCohomologyMackeyCompositionGeometry LinkingCommaNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPGroupCohomologyPullback DPGroupCohomologyOrbitCoefficient
  DPGroupCohomologyTransferNative DPGroupCohomologyTransferTower
  DPGroupCohomologyTransferCovarianceSquare DPGroupCohomologyMackeyPushBase
  DPGroupCohomologyMackeyCompositionGeometry DPLinkingCommaNaturality.

Module DPGroupCohomologyMackeyPushComposition.
Section Composition.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q T : {group S}.
Variable f : DPFusionSystem.arrow F P Q.
Variable g : DPFusionSystem.arrow F Q T.
Local Notation fg := (DPFusionSystem.arrow_compose f g).
Local Notation I := (DPFusion.image (val f)).
Local Notation J := (DPFusion.image (val g)).
Local Notation K := (DPFusion.image (val fg)).
Local Notation k := (inverse_composite_image f g).

Lemma inverse_composite_group_value (x : [subg K]) :
  val (arrow_group_hom k x) =
    DPFusion.map_morphism (DPFusion.inverse (val g)) (val x).
Proof. exact: inverse_composite_image_value (valP x). Qed.

Lemma inverse_image_group_value (x : [subg J]) :
  val (arrow_group_hom (DPFusionMackey.inverse_arrow g) x) =
    DPFusion.map_morphism (DPFusion.inverse (val g)) (val x).
Proof. reflexivity. Qed.

Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.

Lemma inverse_transfer_square :
  module_hom_comp (raw_pull A n k) (transfer A (composite_image_sub_image f g) n) =
  module_hom_comp (transfer A (DPFusion.image_sub (val f)) n)
    (raw_pull A n (DPFusionMackey.inverse_arrow g)).
Proof.
exact (@transfer_covariance_named R S S K J (composite_image_sub_image f g)
  (DPFusion.map_morphism (DPFusion.inverse (val g)))
  (DPFusion.map_injm (DPFusion.inverse (val g))) I Q (DPFusion.image_sub (val f))
  (arrow_group_hom k) (arrow_group_hom (DPFusionMackey.inverse_arrow g))
  (inverse_image_on_composite f g) (inverse_image_on_image g)
  inverse_composite_group_value inverse_image_group_value A n).
Qed.

Theorem raw_push_compose :
  raw_push A n fg = module_hom_comp (raw_push A n f) (raw_push A n g).
Proof.
apply module_hom_ext => z.
have hs := congr1 (fun u => module_hom_fun u
    (module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow f)) z)) inverse_transfer_square.
change (module_hom_fun (transfer A (composite_image_sub_image f g) n)
    (module_hom_fun (raw_pull A n k)
      (module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow f)) z)) =
  module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow g))
    (module_hom_fun (transfer A (DPFusion.image_sub (val f)) n)
      (module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow f)) z))) in hs.
have hf := congr1 (fun u => module_hom_fun u z)
  (@raw_pull_compose S F R A n K I P k (DPFusionMackey.inverse_arrow f)).
rewrite inverse_composite_factorization in hf.
change (module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow fg)) z =
  module_hom_fun (raw_pull A n k)
    (module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow f)) z)) in hf.
change (module_hom_fun (transfer A (DPFusion.image_sub (val fg)) n)
    (module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow fg)) z) =
  module_hom_fun (transfer A (DPFusion.image_sub (val g)) n)
    (module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow g))
      (module_hom_fun (transfer A (DPFusion.image_sub (val f)) n)
        (module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow f)) z)))).
rewrite -hs -hf.
exact (congr1 (fun u => module_hom_fun u
  (module_hom_fun (raw_pull A n (DPFusionMackey.inverse_arrow fg)) z))
  (@transfer_tower R S K J T (composite_image_sub_image f g)
    (DPFusion.image_sub (val g)) A n)).
Qed.

End Composition.
End DPGroupCohomologyMackeyPushComposition.
