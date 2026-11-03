(** The image of chain automorphisms at the top is exactly the inverse
    image of the actual fusion chain stabilizer. *)
From mathcomp Require Import all_boot all_fingroup action boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionSaturation FusionAutomorphisms.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingSystemAutomorphismProjection LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainStabilizer LinkingChainAutomorphismStabilizerRestrictions.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains
  DPLinkingChainAutomorphisms DPNormalizerChainStabilizer
  DPLinkingChainStabilizerRestrictions.
Local Open Scope group_scope.
Local Open Scope action_scope.

Module DPLinkingChainStabilizer.
Section Stabilizer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation I := 'I_(length c).+1.
Local Notation G := (automorphism_group L (top c)).
Local Notation C := (chain_automorphism_group L c).
Local Notation AF := (DPFusionSaturation.aut_group F (val (top c))).
Local Notation H := [subg AF]%type.
Local Notation pr := (DPLinkingAutomorphismProjection.projection L (top c)).

Definition top_morphism : {morphism [set: C] >-> G} := projection_morphism L ord_max.

Lemma top_morphism_apply (a : C) : top_morphism a = projection ord_max a.
Proof. reflexivity. Qed.

Lemma top_projection_action (a : C) (i : I) x (hx : x \in subgroup c i) :
  DPFusion.map_fun (val (linking_projection L (top_morphism a))) x =
    DPFusion.map_fun (val (linking_projection L (projection i a))) x.
Proof.
have hs := @projection_square S F L c a i ord_max (leq_ord i).
have hp := congr1 (@linking_projection S F L (entry c i) (top c)) hs.
rewrite !projection_compose in hp.
have he := congr1 (fun f : DPFusionSystem.arrow F (subgroup c i) (val (top c)) =>
  DPFusion.map_fun (val f) x) hp.
have hi : val (linking_projection L (@chain_inclusion S F L c i ord_max (leq_ord i))) =
    DPFusion.inclusion (@entry_mono S F c i ord_max (leq_ord i)) := projection_inclusion _ _.
change (DPFusion.map_fun (DPFusion.compose (val (linking_projection L (projection i a)))
    (val (linking_projection L (@chain_inclusion S F L c i ord_max (leq_ord i))))) x =
  DPFusion.map_fun (DPFusion.compose (val (linking_projection L (@chain_inclusion S F L c i ord_max (leq_ord i))))
    (val (linking_projection L (projection ord_max a)))) x) in he.
by rewrite hi !DPFusion.compose_in // !DPFusion.inclusion_in ?DPFusion.map_into // in he.
Qed.

Theorem top_projection_stabilizes (a : C) : val (pr (top_morphism a)) \in fusion_stabilizer c.
Proof.
apply/setIP; split; first exact: valP.
apply/bigcapP=> i _; rewrite !inE; apply/subsetP=> x hx; rewrite inE /=.
change (is_true (val (pr (top_morphism a)) x \in subgroup c i)).
rewrite (DPLinkingAutomorphismProjection.projection_apply _
  (subsetP (@entry_sub_top S F c i) _ hx)) (top_projection_action a hx).
exact: DPFusion.map_into _ hx.
Qed.

Definition fusion_stabilizer_subgroup : {group H} :=
  ((@sgval _ AF) @*^-1 (fusion_stabilizer c))%G.

Definition top_stabilizer : {group G} := (pr @*^-1 fusion_stabilizer_subgroup)%G.

Lemma fusion_stabilizer_subgroup_mem (a : H) :
  (a \in fusion_stabilizer_subgroup) = (val a \in fusion_stabilizer c).
Proof. by rewrite /fusion_stabilizer_subgroup !inE. Qed.

Lemma top_stabilizer_mem (a : G) :
  (a \in top_stabilizer) = (val (pr a) \in fusion_stabilizer c).
Proof. by rewrite /top_stabilizer /fusion_stabilizer_subgroup !inE. Qed.

Theorem top_image : top_morphism @* [set: C] = top_stabilizer.
Proof.
apply/setP=> a; rewrite top_stabilizer_mem; apply/morphimP/idP.
- move=> [b _ _ ->]; exact: top_projection_stabilizes.
- move=> ha; exists (@compatible_lift S F L c a ha); [by rewrite inE | by rewrite inE |].
  symmetry; exact: compatible_lift_top.
Qed.

Theorem top_morphism_injective : injective top_morphism.
Proof. exact: top_projection_injective. Qed.

Theorem top_morphism_injm : 'injm top_morphism.
Proof. apply/injmP=> a b _ _; exact: top_morphism_injective. Qed.

Theorem top_isom : isom [set: C] top_stabilizer top_morphism.
Proof. apply/isomP; split; [exact: top_morphism_injm | exact: top_image]. Qed.
End Stabilizer.
End DPLinkingChainStabilizer.

Check DPLinkingChainStabilizer.top_image.
Check DPLinkingChainStabilizer.top_isom.
Print Assumptions DPLinkingChainStabilizer.top_image.
Print Assumptions DPLinkingChainStabilizer.top_isom.
