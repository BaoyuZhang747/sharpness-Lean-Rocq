(** A genuine chain conjugacy extends over the source simultaneous normalizer
    after a Sylow adjustment preserving every target chain entry. *)
From mathcomp Require Import all_boot all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainNormalizer
  NormalizerChainIndices NormalizerChainExtensions NormalizerChainRelations
  NormalizerChainConjugacy NormalizerChainStabilizer NormalizerProjectionCommaSylow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionAutomorphisms DPLinkingChains DPNormalizerChain
  DPNormalizerChainIndices DPNormalizerChainExtensions DPNormalizerChainRelations
  DPNormalizerChainConjugacy DPNormalizerChainStabilizer DPNormalizerProjectionCommaSylow.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaChainExtension.
Section Transport.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.
Variable e : selector c d.
Variable f : DPFusion.map (val (top c)) (val (top d)).
Variable hf : DPFusionSystem.allowed F f.
Variable onto : image f = val (top d).
Variable images : forall i, map_morphism f @* subgroup c (index e i) = subgroup d i.

Lemma entry_image_membership i x (hx : x \in val (top c)) :
  (f x \in subgroup d i) = (x \in subgroup c (index e i)).
Proof.
rewrite -(images i); apply/idP/idP.
- move/morphimP=> [y hy hiy hxy].
  have hi := elimT injmP (DPFusion.map_injm f).
  have -> : x = y := hi x y hx hy hxy; exact hiy.
- move=> hi; exact: mem_morphim hx hi.
Qed.

Lemma transported_stabilizer_sub :
  aut_transport_group f (fusion_stabilizer c) \subset fusion_stabilizer d.
Proof.
apply/subsetP=> b /morphimP[a _ ha ->].
have /fusion_stabilizerP[hFa hfix] := ha.
have hAa := subsetP (DPFusionSaturation.aut_group_sub F (val (top c))) _ hFa.
have hFb := aut_transport_allowed hf hFa; rewrite onto in hFb.
have hAb := aut_transport_mem f a; rewrite onto in hAb.
apply/fusion_stabilizerP; split=> // i y.
case hy : (y \in val (top d)).
- rewrite -onto in hy; have /morphimP[x hx _ ->] := hy.
  have hax := Aut_closed hAa hx.
  rewrite (aut_transportE f hAa hx) (entry_image_membership i hax)
    (entry_image_membership i hx); exact (hfix (index e i) x).
- by rewrite (out_Aut hAb (negbT hy)).
Qed.
End Transport.

Section Extension.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.
Variable a : chain_witness c d.
Variable ba : bijective (index (indices a)).
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable sylD : p.-Sylow(fusion_stabilizer d)
  (DPFusionSaturation.ambient_aut_group (val (top d)) :&: fusion_stabilizer d).

Theorem chain_conjugacy_normalizer_extension :
  exists (V : {group S}) (g : DPFusion.map V [set: S]%G),
    val (top c) \subset V /\ normalizer c \subset V /\ DPFusionSystem.allowed F g /\
    forall i, map_morphism g @* subgroup c (index (indices a) i) = subgroup d i.
Proof.
have hKT := @transported_stabilizer_sub S F c d (indices a) (top_map ba)
  (top_map_allowed ba) (top_map_image ba) (top_map_entry_images ba).
have [b [hb [V [g [hPV [hNV [hg he]]]]]]] :=
  @exists_stabilizer_adjusted_extension S F p hS (val (top c)) (val (top d))
    (top_map ba) (top_map_allowed ba) (top_map_image ba)
    (fusion_stabilizer c) (fusion_stabilizer d) (fusion_stabilizer_sub d) hKT sylD
    sat (valP (top d)).
have /fusion_stabilizerP[_ hfix] := hb.
exists V, g; split=> //; split.
- by rewrite normalizer_eq_k_normalizer.
- split=> // i; apply/setP=> y; apply/morphimP/idP.
  + move=> [x hv hxi ->]; rewrite map_morphismE (he x (subsetP (@entry_sub_top S F c _) _ hxi)).
    rewrite hfix -(top_map_entry_images ba i).
    exact: mem_morphim (subsetP (@entry_sub_top S F c _) _ hxi) hxi.
  + move=> hy.
    have hby : b^-1 y \in subgroup d i by rewrite -(hfix i (b^-1 y)) permKV.
    rewrite -(top_map_entry_images ba i) in hby.
    have /morphimP[x hx hxi ex] := hby.
    rewrite map_morphismE in ex.
    have hv := subsetP hPV _ hx.
    exists x=> //; rewrite map_morphismE (he x hx).
    change (y = b (top_map ba x)); rewrite -ex permKV; reflexivity.
Qed.
End Extension.
End DPNormalizerProjectionCommaChainExtension.
