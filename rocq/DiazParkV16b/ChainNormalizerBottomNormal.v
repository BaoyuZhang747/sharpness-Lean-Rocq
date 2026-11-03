(** The literal bottom subgroup has a normal image in the actual compatible
    linking-chain automorphism group.  No saturation is used here. *)
From mathcomp Require Import all_boot all_fingroup pgroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionCentralizerMaps.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainNormalizer
  NormalizerChainTransporter NormalizerChainEmbedding LinkingChainAutomorphismStabilizer
  LinkingSystemNormalizerActionRange FiniteGroupFusionEmbeddingImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains
  DPLinkingChainAutomorphisms DPNormalizerChain DPNormalizerChainTransporter
  DPNormalizerChainEmbedding DPLinkingChainStabilizer.
Local Open Scope group_scope.

Module DPChainNormalizerBottom.
Section Bottom.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation N := [subg (normalizer c)]%type.
Local Notation C := (chain_automorphism_group L c).
Local Notation E := (normalizer_embedding_morphism L c).

Definition bottom_subgroup : {group N} :=
  ((@sgval _ (normalizer c)) @*^-1 (val (bottom c)))%G.

Lemma bottom_subgroup_mem (x : N) :
  (x \in bottom_subgroup) = (val x \in val (bottom c)).
Proof. by rewrite /bottom_subgroup !inE. Qed.

Lemma bottom_subgroup_ambient : DPFusionSubgroup.ambient bottom_subgroup = val (bottom c).
Proof.
apply val_inj; apply: morphpreK.
by rewrite im_sgval; exact: bottom_sub_normalizer.
Qed.

Definition bottom_element (x : [subg (val (bottom c))]) : N :=
  Sub (val x) (subsetP (bottom_sub_normalizer c) _ (valP x)).

Lemma bottom_element_mem x : bottom_element x \in bottom_subgroup.
Proof. rewrite bottom_subgroup_mem; exact (valP x). Qed.

Definition bottom_embedding (x : [subg (val (bottom c))]) : C :=
  normalizer_embedding L (bottom_element x).

Definition bottom_image : {group C} := (E @* bottom_subgroup)%G.

Lemma bottom_embedding_mem x : bottom_embedding x \in bottom_image.
Proof. exact (mem_morphim E (in_setT _) (bottom_element_mem x)). Qed.

Lemma bottom_embedding_top x :
  top_morphism L c (bottom_embedding x) =
  distinguished L (Sub (val x)
    (subsetP (@entry_sub_top S F c ord0) _ (valP x))).
Proof.
change (projection ord_max (normalizer_embedding L (bottom_element x)) =
  distinguished L (Sub (val x) (subsetP (@entry_sub_top S F c ord0) _ (valP x)))).
rewrite normalizer_embedding_projection.
rewrite /coordinate /normalizer_map /distinguished.
congr (linking_transporter L _); apply val_inj; reflexivity.
Qed.

Theorem bottom_embedding_conjugation (a : C) (x : [subg (val (bottom c))]) :
  bottom_embedding x ^ a =
  bottom_embedding (arrow_element (linking_projection L (projection ord0 a)) x).
Proof.
apply: (@top_morphism_injective S F L c).
rewrite (morphJ (top_morphism L c) (in_setT _) (in_setT _)) !bottom_embedding_top.
rewrite -DPLinkingNormalizerActionRange.distinguished_conjugation.
congr (distinguished L _); apply val_inj.
exact (@top_projection_action S F L c a ord0 (val x) (valP x)).
Qed.

Theorem bottom_image_normal : bottom_image <| [set: C].
Proof.
apply/andP; split; first exact: subsetT.
apply/subsetP=> a _; apply/normP/eqP.
rewrite eqEcard cardJg leqnn andbT.
apply/subsetP=> z /imsetP[y /morphimP[x _ hx ->] ->].
have hxB : val x \in val (bottom c) by move: hx; rewrite bottom_subgroup_mem.
pose bx : [subg (val (bottom c))] := Sub (val x) hxB.
have he : E x = bottom_embedding bx.
  congr (normalizer_embedding L _); apply val_inj; reflexivity.
by rewrite he bottom_embedding_conjugation; exact: bottom_embedding_mem.
Qed.

Theorem bottom_image_sub : bottom_image \subset
  DPFiniteGroupFusionEmbeddingImage.image_group E.
Proof. exact (morphimS E (subsetT bottom_subgroup)). Qed.

Theorem bottom_image_pgroup (p : nat) : p.-group [set: S] -> p.-group bottom_image.
Proof.
move=> hS; apply: morphim_pgroup.
have hN : p.-group [set: N].
  rewrite /pgroup cardsT card_sub; exact (pgroupS (subsetT (normalizer c)) hS).
exact: pgroupS (subsetT bottom_subgroup) hN.
Qed.

End Bottom.
End DPChainNormalizerBottom.

Print Assumptions DPChainNormalizerBottom.bottom_embedding_conjugation.
Print Assumptions DPChainNormalizerBottom.bottom_image_normal.
Print Assumptions DPChainNormalizerBottom.bottom_image_pgroup.
