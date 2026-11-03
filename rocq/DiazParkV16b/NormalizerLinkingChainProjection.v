(** The actual linking-chain category projects to the actual quotient
    normalizer index. Every arrow supplies its own simultaneous fusion witness. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndices NormalizerChainExtensions NormalizerChainRelations NormalizerChainIndexCategory
  LinkingChainRestrictionMaps LinkingChainRestrictionUniqueness NormalizerLinkingEvaluationImage
  NormalizerLinkingChainCategory.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPCentricLinking DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChainIndices
  DPNormalizerChainExtensions DPNormalizerChainRelations DPNormalizerChainIndex
  DPLinkingChainRestrictionMaps DPLinkingChainRestrictionUniqueness
  DPNormalizerLinkingEvaluationImage DPNormalizerLinkingChainCategory.
Local Open Scope group_scope.

Module DPNormalizerLinkingChainProjection.
Section Projection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Lemma linking_isomorphism_image (P Q : DPFusionOrbit.centric_object F)
    (e : @isomorphism (linking_category L) P Q) :
  DPFusion.image (val (linking_projection L (iso_hom e))) = val Q.
Proof. exact (@image_eq_of_card S F L P Q (iso_hom e) (@linking_iso_card S F L P Q e)). Qed.

Section Witness.
Variables c d : chain F.
Variable f : chain_map L c d.
Local Notation e := (selected_indices f).
Local Notation V := (subgroup c (index e ord_max)).

Definition projected_entry (i : 'I_(length d).+1) :=
  val (linking_projection L (iso_hom (entry_isomorphism f i))).

Lemma projected_entry_image i : DPFusion.image (projected_entry i) = subgroup d i.
Proof. exact: linking_isomorphism_image. Qed.

Definition selected_entry_sub (i : 'I_(length d).+1) : subgroup c (index e i) \subset V :=
  @entry_mono S F c _ _ (@index_mono S F c d e i ord_max (leq_ord i)).

Lemma projected_entry_top i x (hx : x \in subgroup c (index e i)) :
  projected_entry ord_max x = projected_entry i x.
Proof.
have hs := congr1 (fun a : linking_hom L (entry c (index e i)) (entry d ord_max) =>
  val (linking_projection L a) x) (@entry_square S F L c d f i ord_max (leq_ord i)).
rewrite !projection_compose in hs.
change (DPFusion.compose
  (val (linking_projection L (@chain_inclusion S F L c _ _ (@index_mono S F c d e i ord_max (leq_ord i)))))
  (projected_entry ord_max) x =
  DPFusion.compose (projected_entry i)
  (val (linking_projection L (@chain_inclusion S F L d i ord_max (leq_ord i)))) x) in hs.
rewrite /chain_inclusion !projection_inclusion !compose_in // !inclusion_in ?map_into // in hs.
Qed.

Definition witness_extension_map : DPFusion.map V [set: S]%G :=
  DPFusion.compose (projected_entry ord_max) (DPFusion.inclusion (subsetT (subgroup d ord_max))).

Lemma witness_extension_allowed : DPFusionSystem.allowed F witness_extension_map.
Proof.
apply: DPFusionSystem.composition_closed (valP (linking_projection L (iso_hom (entry_isomorphism f ord_max)))) _.
exact: DPFusionSystem.inclusion_allowed.
Qed.

Lemma witness_extension_entry i x (hx : x \in subgroup c (index e i)) :
  witness_extension_map x = projected_entry i x.
Proof.
have hxV : x \in V := subsetP (selected_entry_sub i) x hx.
rewrite /witness_extension_map compose_in // inclusion_in ?map_into //.
exact: projected_entry_top hx.
Qed.

Lemma witness_entry_images i : map_morphism witness_extension_map @* subgroup c (index e i) = subgroup d i.
Proof.
have hset := congr1 (fun P : {group S} => (P : {set S})) (projected_entry_image i).
rewrite -hset.
change (map_morphism witness_extension_map @* subgroup c (index e i) =
  map_morphism (projected_entry i) @* subgroup c (index e i)).
apply: eq_in_morphim.
- by rewrite (setIidPr (selected_entry_sub i)) setIid.
- move=> x hx; rewrite !map_morphismE; exact: witness_extension_entry hx.
Qed.

Definition arrow_witness : chain_witness c d.
Proof.
refine (@Build_extension S F c d 1%G 1%G (DPFusion.identity 1%G) e V
  (sub1G V) (subxx V) witness_extension_map witness_extension_allowed _ witness_entry_images).
move=> x /set1P ->; by rewrite !map_one.
Defined.

Lemma arrow_subconjugate : subconjugate c d.
Proof. apply/subconjugateP; exact (inhabits arrow_witness). Qed.

End Witness.

Definition projection_arrow (c d : chain F) (f : chain_map L c d) :
  index_hom (chain_class c) (chain_class d).
Proof.
apply hom_of_relation; rewrite class_relation; exact: arrow_subconjugate.
Defined.

Definition projection : functor (chain_category L) (index_category F).
Proof.
refine (@Build_functor (chain_category L) (index_category F) (@chain_class S F)
  (fun c d f => projection_arrow f) _ _); intros; exact: index_hom_unique.
Defined.

Lemma projection_object (c : chain F) : fobj projection c = chain_class c.
Proof. reflexivity. Qed.

Lemma projection_map (c d : chain F) (f : chain_map L c d) :
  fmap projection f = projection_arrow f.
Proof. reflexivity. Qed.

End Projection.
End DPNormalizerLinkingChainProjection.
