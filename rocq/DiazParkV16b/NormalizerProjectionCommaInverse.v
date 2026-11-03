(** Invert an actual simultaneous extension on the target acting/top join.
    Only the given acting map must be onto; the larger original extension
    carrier need not be the minimal join and no inverse extension is assumed. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices NormalizerChainExtensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionConjugacy DPLinkingChains DPNormalizerChainIndices DPNormalizerChainExtensions.
Local Open Scope group_scope.

Module DPNormalizerProjectionCommaInverse.
Section Inverse.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Variable a : extension c d f.
Variable onto : image f = Q.
Local Notation g := (extension_map a).
Local Notation J := (Q <*> val (top d))%G.

Lemma acting_sub_extension_image : Q \subset image g.
Proof.
apply/subsetP=> y hy.
have hy' : y \in image f by rewrite onto.
have /morphimP[x _ hx ->] := hy'.
rewrite map_morphismE -(on_acting a hx).
exact: image_mem (subsetP (acting_sub a) _ hx).
Qed.

Lemma top_sub_extension_image : val (top d) \subset image g.
Proof.
rewrite -(entry_images a ord_max).
exact: morphimS (entry_sub_carrier a ord_max).
Qed.

Lemma target_join_sub_extension_image : J \subset image g.
Proof. by rewrite join_subG acting_sub_extension_image top_sub_extension_image. Qed.

Definition inverse_join_map : DPFusion.map J [set: S]%G :=
  DPFusion.compose (restrict (DPFusion.inverse g) target_join_sub_extension_image)
    (inclusion (subsetT (carrier a))).

Lemma inverse_join_map_allowed : DPFusionSystem.allowed F inverse_join_map.
Proof.
apply: DPFusionSystem.composition_closed; last exact: DPFusionSystem.inclusion_allowed.
apply: DPFusionSystem.restriction_allowed; exact: DPFusionSystem.inverse_closed (extension_allowed a).
Qed.

Lemma inverse_join_mapE x (hx : x \in J) : inverse_join_map x = DPFusion.inverse g x.
Proof.
rewrite /inverse_join_map compose_in // inclusion_in ?map_into // restrict_in //.
Qed.

Lemma inverse_join_on_acting x (hx : x \in Q) : inverse_join_map x = onto_inverse onto x.
Proof.
rewrite inverse_join_mapE ?(subsetP (joing_subl Q _) _ hx) //.
rewrite -onto in hx; have /morphimP[y _ hy ex] := hx.
rewrite map_morphismE in ex; rewrite ex onto_inverse_cancel // -(on_acting a hy).
exact: inverse_cancel (subsetP (acting_sub a) _ hy).
Qed.

Lemma inverse_join_entry_images i :
  map_morphism inverse_join_map @* subgroup d i = subgroup c (index (indices a) i).
Proof.
apply/setP=> y; apply/morphimP/idP.
- move=> [x hx hxi ->]; rewrite map_morphismE inverse_join_mapE //.
  rewrite -(entry_images a i) in hxi.
  have /morphimP[z hz hzi ex] := hxi; rewrite map_morphismE in ex.
  by rewrite ex inverse_cancel.
- move=> hy.
  have hyV := subsetP (entry_sub_carrier a i) _ hy.
  have hgy : g y \in subgroup d i.
    rewrite -(entry_images a i); exact: mem_morphim hyV hy.
  have hgyJ : g y \in J := subsetP (joing_subr Q _) _
    (subsetP (@entry_sub_top S F d i) _ hgy).
  exists (g y)=> //.
  rewrite map_morphismE inverse_join_mapE // inverse_cancel //.
Qed.

Definition inverse_selected : extension d (selected_chain (indices a)) (onto_inverse onto).
Proof.
refine (@Build_extension S F d (selected_chain (indices a)) Q P (onto_inverse onto)
  (DPNormalizerChainIndices.identity d) J (joing_subl _ _) _
  inverse_join_map inverse_join_map_allowed inverse_join_on_acting _).
- rewrite identity_index; exact: joing_subr.
- move=> i; rewrite identity_index /subgroup selected_chain_entry.
  exact: inverse_join_entry_images.
Defined.
End Inverse.
End DPNormalizerProjectionCommaInverse.
