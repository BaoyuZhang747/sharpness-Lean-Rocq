(** Whole-chain fusion conjugacy extracted from a bijective selection,
    including its actual allowed inverse on the top subgroup. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy FusionSaturationImage.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices
  NormalizerChainIndexIsomorphisms NormalizerChainExtensions NormalizerChainRelations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionConjugacy DPLinkingChains DPNormalizerChainIndices
  DPNormalizerChainIndexIsomorphisms DPNormalizerChainExtensions DPNormalizerChainRelations.
Local Open Scope group_scope.

Module DPNormalizerChainConjugacy.
Section TopInverse.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.
Variable a : chain_witness c d.
Hypothesis ba : bijective (index (indices a)).

Lemma top_sub_carrier : val (top c) \subset carrier a.
Proof. have h := chain_sub a; by rewrite (index_top ba) in h. Qed.

Definition top_restriction := restrict (extension_map a) top_sub_carrier.

Lemma top_restriction_image : image top_restriction = val (top d).
Proof.
apply val_inj.
change (map_morphism (restrict (extension_map a) top_sub_carrier) @* val (top c) = val (top d)).
rewrite /restrict of_morphism_image im_restrm.
have h := entry_images a ord_max; by rewrite (index_top ba) in h.
Qed.

Lemma top_restriction_sub : image top_restriction \subset val (top d).
Proof. by rewrite top_restriction_image. Qed.

Definition top_map : DPFusion.map (val (top c)) (val (top d)) :=
  corestrict top_restriction_sub.

Lemma top_mapE x : x \in val (top c) -> top_map x = extension_map a x.
Proof. move=> hx; by rewrite /top_map corestrict_in // /top_restriction restrict_in. Qed.

Lemma top_map_allowed : DPFusionSystem.allowed F top_map.
Proof.
apply: DPFusionSystem.corestriction_allowed.
exact: DPFusionSystem.restriction_allowed (extension_allowed a).
Qed.

Lemma top_map_image : image top_map = val (top d).
Proof. rewrite /top_map DPFusionSaturationImage.image_corestrict; exact: top_restriction_image. Qed.

Lemma top_map_entry_images i :
  map_morphism top_map @* subgroup c (index (indices a) i) = subgroup d i.
Proof.
rewrite -(entry_images a i); apply: eq_in_morphim.
- by rewrite (setIidPr (@entry_sub_top S F c _))
    (setIidPr (entry_sub_carrier a i)).
- move=> x hx; exact: top_mapE (subsetP (@entry_sub_top S F c _) _ hx).
Qed.

Definition inverse_top_map : DPFusion.map (val (top d)) (val (top c)) :=
  onto_inverse top_map_image.

Lemma inverse_top_allowed : DPFusionSystem.allowed F inverse_top_map.
Proof. exact: onto_inverse_allowed top_map_allowed. Qed.

Lemma inverse_top_entry_images j :
  map_morphism inverse_top_map @* subgroup d (inverse_index ba j) = subgroup c j.
Proof.
have he := top_map_entry_images (inverse_index ba j).
rewrite inverse_index_right in he.
apply/setP=> y; apply/morphimP/idP.
- move=> [x hx hxi ->]; rewrite map_morphismE /inverse_top_map.
  rewrite -he in hxi; have /morphimP[z hz hzc ex] := hxi.
  rewrite map_morphismE in ex; rewrite ex onto_inverse_cancel //.
- move=> hy; have hc := subsetP (@entry_sub_top S F c j) _ hy.
  have hd : top_map y \in subgroup d (inverse_index ba j).
    rewrite -he; exact: mem_morphim hc hy.
  exists (top_map y); [exact: map_into hc | exact hd |].
  rewrite map_morphismE /inverse_top_map; exact: esym (onto_inverse_cancel top_map_image hc).
Qed.

Definition inverse_extension_map : DPFusion.map (val (top d)) [set: S]%G :=
  DPFusion.compose inverse_top_map (inclusion (subsetT (val (top c)))).

Lemma inverse_extension_mapE x : x \in val (top d) ->
  inverse_extension_map x = inverse_top_map x.
Proof. move=> hx; by rewrite /inverse_extension_map compose_in // inclusion_in ?map_into. Qed.

Definition inverse_witness : chain_witness d c.
Proof.
refine (@Build_extension S F d c 1%G 1%G (DPFusion.identity 1%G)
  (inverse_selector ba) (val (top d)) (sub1G _) (@entry_sub_top S F d _)
  inverse_extension_map _ _ _).
- apply: DPFusionSystem.composition_closed inverse_top_allowed _.
  exact: DPFusionSystem.inclusion_allowed.
- move=> x /set1P ->; by rewrite !map_one.
- move=> j; rewrite inverse_selector_index -(inverse_top_entry_images j).
  apply: eq_morphim=> x hx; exact: inverse_extension_mapE hx.
Defined.

Lemma inverse_witness_bijective : bijective (index (indices inverse_witness)).
Proof. exact: inverse_selector_bijective. Qed.

End TopInverse.

Section Conjugacy.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition conjugate (c d : chain F) :=
  asbool (exists a : chain_witness c d, bijective (index (indices a))).

Lemma conjugateP (c d : chain F) : reflect
  (exists a : chain_witness c d, bijective (index (indices a))) (conjugate c d).
Proof. exact: asboolP. Qed.

Theorem conjugate_top_iff (c d : chain F) : conjugate c d <->
  exists e : selector c d, bijective (index e) /\
    exists f : DPFusion.map (val (top c)) (val (top d)),
      DPFusionSystem.allowed F f /\
      forall i, map_morphism f @* subgroup c (index e i) = subgroup d i.
Proof.
split.
- move/conjugateP=> [a ha].
  exists (indices a); split=> //; exists (top_map ha); split.
  + exact: top_map_allowed.
  + exact: top_map_entry_images.
- move=> [e [he [f [hf hi]]]].
  pose b := DPFusion.compose f (inclusion (subsetT (val (top d)))).
  have hb : DPFusionSystem.allowed F b :=
    DPFusionSystem.composition_closed hf (DPFusionSystem.inclusion_allowed F _).
  have h1 : forall x, x \in 1%G -> b x = DPFusion.identity 1%G x.
    move=> x /set1P ->; by rewrite !map_one.
  have him : forall i, map_morphism b @* subgroup c (index e i) = subgroup d i.
    move=> i; rewrite -(hi i); apply: eq_morphim=> x hx.
    by rewrite map_morphismE /b compose_in // inclusion_in ?map_into.
  apply/conjugateP.
  exists (@Build_extension S F c d 1%G 1%G (DPFusion.identity 1%G)
    e (val (top c)) (sub1G _) (@entry_sub_top S F c _) b hb h1 him).
  exact he.
Qed.

Lemma conjugate_subconjugate (c d : chain F) : conjugate c d -> subconjugate c d.
Proof. move/conjugateP=> [a _]; apply/subconjugateP; exact: inhabits a. Qed.

Lemma conjugate_reverse (c d : chain F) : conjugate c d -> conjugate d c.
Proof.
move/conjugateP=> [a ha]; apply/conjugateP.
exists (inverse_witness ha); exact: inverse_witness_bijective.
Qed.

Theorem conjugate_iff_mutual (c d : chain F) : conjugate c d = mutually_subconjugate c d.
Proof.
apply/idP/idP.
- move=> h; apply/andP; split.
  + exact: conjugate_subconjugate h.
  + exact: conjugate_subconjugate (conjugate_reverse h).
- move=> h; have hd := mutually_subconjugate_length h.
  have /andP[/subconjugateP[a] _] := h.
  apply/conjugateP; exists a; exact: equal_length_bijective hd.
Qed.

End Conjugacy.
End DPNormalizerChainConjugacy.
