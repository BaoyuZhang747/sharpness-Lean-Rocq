(** Fusion-automorphism transport reflects allowed automorphisms along every
    actual fusion injection, and identifies the stabilizer of its image chain. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionAutomorphisms.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainStabilizer
  NormalizerChainTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionAutomorphisms DPLinkingChains DPNormalizerChainStabilizer
  DPNormalizerChainTransport.
Local Open Scope group_scope.

Module DPNormalizerChainTransportStabilizer.
Section Automorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Hypothesis hf : DPFusionSystem.allowed F f.

Lemma inverse_image : DPFusion.image (DPFusion.inverse f) = P.
Proof.
apply val_inj; change (DPFusion.map_morphism (DPFusion.inverse f) @* DPFusion.image f = P).
by rewrite /DPFusion.inverse DPFusion.of_morphism_image im_invm.
Qed.

Lemma aut_transport_inverse a (ha : a \in Aut P) :
  aut_transport (DPFusion.inverse f) (aut_transport f a) = a.
Proof.
have hh := aut_transport_mem (DPFusion.inverse f) (aut_transport f a).
rewrite inverse_image in hh.
apply: (eq_Aut hh ha)=> x hx.
have hfx := DPFusion.image_mem f hx.
have hax := Aut_closed ha hx.
rewrite -{1}(DPFusion.inverse_cancel f hx).
rewrite (aut_transportE (DPFusion.inverse f) (aut_transport_mem f a) hfx).
by rewrite (aut_transportE f ha hx) DPFusion.inverse_cancel.
Qed.

Theorem aut_transport_allowed_reflect a (ha : a \in Aut P) :
  aut_transport f a \in DPFusionSaturation.aut_group F (DPFusion.image f) ->
    a \in DPFusionSaturation.aut_group F P.
Proof.
move=> hab.
have h := aut_transport_allowed (DPFusionSystem.inverse_closed hf) hab.
by rewrite inverse_image aut_transport_inverse in h.
Qed.
End Automorphisms.

Section Stabilizers.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.
Variable Q : {group S}.
Variable f : DPFusion.map (val (top c)) Q.
Hypothesis hf : DPFusionSystem.allowed F f.
Local Notation t := (@transport S F c Q f hf).
Local Notation P := (val (top c)).

Lemma stabilizer_transport_mem a (ha : a \in fusion_stabilizer c) :
  aut_transport f a \in fusion_stabilizer t.
Proof.
have /fusion_stabilizerP[hFa hfix] := ha.
have hAa := subsetP (DPFusionSaturation.aut_group_sub F P) _ hFa.
have hFb := aut_transport_allowed hf hFa.
have hAb := aut_transport_mem f a.
apply/fusion_stabilizerP; split.
- by rewrite transport_top_image.
- move=> i y; case hy : (y \in DPFusion.image f).
  + have /morphimP[x hx _ ->] := hy.
    have hax := Aut_closed hAa hx.
    rewrite (aut_transportE f hAa hx)
      (@transport_mem S F c Q f hf i (a x) hax)
      (@transport_mem S F c Q f hf i x hx).
    exact (hfix i x).
  + by rewrite (out_Aut hAb (negbT hy)).
Qed.

Lemma stabilizer_transport_reflect a (ha : a \in Aut P)
    (hb : aut_transport f a \in fusion_stabilizer t) :
  a \in fusion_stabilizer c.
Proof.
have /fusion_stabilizerP[hFb hfix] := hb.
rewrite transport_top_image in hFb.
have hFa := aut_transport_allowed_reflect hf ha hFb.
apply/fusion_stabilizerP; split=> // i x.
case hx : (x \in P).
- have ht := hfix i (f x).
  have hax := Aut_closed ha hx.
  rewrite (aut_transportE f ha hx)
    (@transport_mem S F c Q f hf i (a x) hax)
    (@transport_mem S F c Q f hf i x hx) in ht.
  exact ht.
- by rewrite (out_Aut ha (negbT hx)).
Qed.

Theorem fusion_stabilizer_transport :
  fusion_stabilizer t = aut_transport_group f (fusion_stabilizer c).
Proof.
apply val_inj; apply/setP=> b; apply/idP/idP.
- move=> hb.
  have hFb := subsetP (fusion_stabilizer_sub t) _ hb.
  have hAb := subsetP (DPFusionSaturation.aut_group_sub F (val (top t))) _ hFb.
  rewrite transport_top_image in hAb.
  have him : b \in Aut_isom (DPFusion.map_injm f) (subxx P) @* Aut P.
    by rewrite im_Aut_isom.
  have /morphimP[a ha _ hab] := him.
  change (b = aut_transport f a) in hab.
  apply/morphimP; exists a=> //.
  exact (stabilizer_transport_reflect ha (eq_ind b
    (fun z => z \in fusion_stabilizer t) hb _ hab)).
- move/morphimP=> [a _ ha ->]; exact: stabilizer_transport_mem.
Qed.

End Stabilizers.
End DPNormalizerChainTransportStabilizer.
