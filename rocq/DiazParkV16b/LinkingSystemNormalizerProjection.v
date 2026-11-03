(** Literal projected values and subgroup images of a linking extension
    with a prescribed restriction square. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking.
Local Open Scope group_scope.

Module DPLinkingNormalizerProjection.
Section Projection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).
Variables U N T : Obj.
Hypothesis hUN : val U \subset val N.
Hypothesis hUT : val U \subset val T.
Variable a : linking_hom L U U.
Variable b : linking_hom L N T.
Hypothesis square : linking_compose L a (inclusion L hUT) =
  linking_compose L (inclusion L hUN) b.

Theorem extension_projection_in x (hx : x \in val U) :
  DPFusion.map_fun (val (linking_projection L b)) x =
    DPFusion.map_fun (val (linking_projection L a)) x.
Proof.
have hp := congr1 (@linking_projection S F L U T) square.
rewrite !projection_compose in hp.
have hn := @projection_inclusion S F L U N hUN.
have ht := @projection_inclusion S F L U T hUT.
change (val (linking_projection L (inclusion L hUN)) = DPFusion.inclusion hUN) in hn.
change (val (linking_projection L (inclusion L hUT)) = DPFusion.inclusion hUT) in ht.
have he := congr1 (fun f : DPFusionSystem.arrow F (val U) (val T) =>
  DPFusion.map_fun (val f) x) hp.
change (DPFusion.map_fun (DPFusion.compose (val (linking_projection L a))
    (val (linking_projection L (inclusion L hUT)))) x =
  DPFusion.map_fun (DPFusion.compose (val (linking_projection L (inclusion L hUN)))
    (val (linking_projection L b))) x) in he.
by rewrite hn ht !DPFusion.compose_in // !DPFusion.inclusion_in ?DPFusion.map_into // in he.
Qed.

Theorem extension_projection_image (R : {group S}) (hRU : R \subset val U)
    (hRN : R \subset val N)
    (hR : forall x, x \in R -> DPFusion.map_fun (val (linking_projection L a)) x \in R) :
  DPFusion.image (DPFusion.restrict (val (linking_projection L b)) hRN) = R.
Proof.
apply val_inj; apply/eqP; rewrite eqEcard; apply/andP; split.
- apply/subsetP=> y /morphimP [x _ hx ->].
  rewrite DPFusion.map_morphismE DPFusion.restrict_in //
    (extension_projection_in (subsetP hRU _ hx)).
  exact: hR.
- rewrite /DPFusion.image (card_injm (DPFusion.map_injm _) (subxx R)); exact: leqnn.
Qed.
End Projection.
End DPLinkingNormalizerProjection.

Print Assumptions DPLinkingNormalizerProjection.extension_projection_in.
Print Assumptions DPLinkingNormalizerProjection.extension_projection_image.
