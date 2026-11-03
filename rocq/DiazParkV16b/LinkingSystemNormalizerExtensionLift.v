(** Correcting a raw fusion extension to a prescribed actual linking
    restriction, using the standard central source fibre. *)
From mathcomp Require Import all_boot all_fingroup center.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem
  LinkingSystemAutomorphisms LinkingSystemFinite LinkingSystemFactorization.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking DPLinkingAutomorphisms DPLinkingFinite DPLinkingFactorization.
Local Open Scope group_scope.

Module DPLinkingNormalizerExtensionLift.
Section Lift.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition overgroup_element (P Q : Obj) (hPQ : val P \subset val Q)
    (x : [subg (val P)]) : [subg (val Q)] := Sub (val x) (subsetP hPQ _ (valP x)).

Lemma distinguished_inclusion_square (P Q : Obj) (hPQ : val P \subset val Q)
    (x : [subg (val P)]) :
  linking_compose L (distinguished L x) (inclusion L hPQ) =
    linking_compose L (inclusion L hPQ) (distinguished L (overgroup_element hPQ x)).
Proof.
rewrite /distinguished /inclusion -!transporter_compose.
congr (linking_transporter L _); apply val_inj.
change (val x * 1 = 1 * val x); by rewrite mulg1 mul1g.
Qed.

Variables U N T : Obj.
Hypothesis hUN : val U \subset val N.
Hypothesis hUT : val U \subset val T.
Variable a : automorphism_group L U.
Variable r : DPFusionSystem.arrow F (val N) (val T).
Hypothesis extends : forall x, x \in val U ->
  DPFusion.map_fun (val r) x = DPFusion.map_fun (val (linking_projection L a)) x.

Lemma raw_extension_square :
  linking_projection L (linking_compose L (inclusion L hUN) (chosen_lift L r)) =
  linking_projection L (linking_compose L a (inclusion L hUT)).
Proof.
rewrite !projection_compose chosen_lift_projection.
have hn := @projection_inclusion S F L U N hUN.
have ht := @projection_inclusion S F L U T hUT.
change (val (linking_projection L (inclusion L hUN)) = DPFusion.inclusion hUN) in hn.
change (val (linking_projection L (inclusion L hUT)) = DPFusion.inclusion hUT) in ht.
apply DPFusionSystem.arrow_ext=> x hx.
change (DPFusion.map_fun (DPFusion.compose (val (linking_projection L (inclusion L hUN))) (val r)) x =
  DPFusion.map_fun (DPFusion.compose (val (linking_projection L a))
    (val (linking_projection L (inclusion L hUT)))) x).
rewrite hn ht !DPFusion.compose_in // !DPFusion.inclusion_in ?DPFusion.map_into //.
exact: extends.
Qed.

Theorem exists_prescribed_extension : exists b : linking_hom L N T,
  linking_compose L a (inclusion L hUT) = linking_compose L (inclusion L hUN) b.
Proof.
have [z [hz _]] := proj1 (@central_fiber S F L U T
  (linking_compose L (inclusion L hUN) (chosen_lift L r))
  (linking_compose L a (inclusion L hUT))) raw_extension_square.
exists (linking_compose L (distinguished L (overgroup_element hUN (center_element z)))
  (chosen_lift L r)).
change (linking_compose L (distinguished L (center_element z))
  (linking_compose L (inclusion L hUN) (chosen_lift L r)) =
  linking_compose L a (inclusion L hUT)) in hz.
rewrite -linking_assoc distinguished_inclusion_square linking_assoc in hz.
exact: esym hz.
Qed.
End Lift.
End DPLinkingNormalizerExtensionLift.

Check DPLinkingNormalizerExtensionLift.exists_prescribed_extension.
Print Assumptions DPLinkingNormalizerExtensionLift.distinguished_inclusion_square.
Print Assumptions DPLinkingNormalizerExtensionLift.exists_prescribed_extension.
