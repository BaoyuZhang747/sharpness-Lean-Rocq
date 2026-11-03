(** Actual simultaneous fusion extensions on selected centric subchains.
    Domains may be larger than the acting/selected-top join; composition
    restricts the first domain to the inverse image of the second. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices
  NormalizerChainExtensionPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPNormalizerChainIndices DPNormalizerChainExtensionPreimages.
Local Open Scope group_scope.

Module DPNormalizerChainExtensions.
Section Extensions.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Record extension (c d : chain F) (P Q : {group S}) (f : DPFusion.map P Q) := {
  indices : selector c d;
  carrier : {group S};
  acting_sub : P \subset carrier;
  chain_sub : subgroup c (index indices ord_max) \subset carrier;
  extension_map : DPFusion.map carrier [set: S]%G;
  extension_allowed : DPFusionSystem.allowed F extension_map;
  on_acting : forall x, x \in P -> extension_map x = f x;
  entry_images : forall i,
    map_morphism extension_map @* subgroup c (index indices i) = subgroup d i
}.

Lemma entry_sub_carrier (c d : chain F) (P Q : {group S}) (f : DPFusion.map P Q)
    (a : extension c d f) i : subgroup c (index (indices a) i) \subset carrier a.
Proof.
apply: subset_trans (chain_sub a).
apply: entry_mono; apply: index_mono; exact: leq_ord.
Qed.

Lemma extension_forces_allowed (c d : chain F) (P Q : {group S}) (f : DPFusion.map P Q)
    (a : extension c d f) : DPFusionSystem.allowed F f.
Proof.
pose r := restrict (extension_map a) (acting_sub a).
have hr : DPFusionSystem.allowed F r :=
  DPFusionSystem.restriction_allowed (acting_sub a) (extension_allowed a).
have hs : image r \subset Q.
  apply/subsetP=> y /morphimP[x _ hx ->].
  rewrite map_morphismE /r restrict_in // (on_acting a hx).
  exact: map_into hx.
have he : corestrict hs = f.
  apply: map_ext=> x hx; by rewrite corestrict_in // /r restrict_in // on_acting.
rewrite -he; exact: DPFusionSystem.corestriction_allowed hr.
Qed.

Definition identity_extension (P : {group S}) (c : chain F) :
    extension c c (DPFusion.identity P).
Proof.
pose V := (P <*> val (top c))%G.
refine (@Build_extension c c P P (DPFusion.identity P)
  (DPNormalizerChainIndices.identity c) V (joing_subl _ _) _
  (inclusion (subsetT V)) (DPFusionSystem.inclusion_allowed F _) _ _).
- rewrite identity_index; exact: joing_subr.
- move=> x hx; rewrite inclusion_in ?(subsetP (joing_subl P _) _ hx) // identity_in //.
- move=> i; rewrite identity_index; apply/setP=> y; apply/morphimP/idP.
  + move=> [x hv hx ->]; by rewrite map_morphismE inclusion_in.
  + move=> hy; have hv : y \in V := subsetP (joing_subr P _) _
      (subsetP (@entry_sub_top S F c i) _ hy).
    exists y=> //; by rewrite map_morphismE inclusion_in.
Defined.

Variables c d t : chain F.
Variables P Q U : {group S}.
Variables f : DPFusion.map P Q.
Variables g : DPFusion.map Q U.
Variable a : extension c d f.
Variable b : extension d t g.

Definition composite_carrier : {group S} := preimage (extension_map a) (carrier b).

Lemma composite_acting_sub : P \subset composite_carrier.
Proof.
apply/subsetP=> x hx; rewrite preimage_mem; apply/andP; split.
- exact: subsetP (acting_sub a) _ hx.
- rewrite (on_acting a hx); exact: subsetP (acting_sub b) _ (map_into f hx).
Qed.

Lemma composite_chain_sub :
  subgroup c (index (DPNormalizerChainIndices.compose (indices a) (indices b)) ord_max)
    \subset composite_carrier.
Proof.
rewrite compose_index; apply/subsetP=> x hx; rewrite preimage_mem.
have ha : x \in carrier a := subsetP (entry_sub_carrier a _) _ hx.
apply/andP; split=> //.
apply (subsetP (chain_sub b) (extension_map a x)).
rewrite -(entry_images a (index (indices b) ord_max)).
exact: mem_morphim ha hx.
Qed.

Definition composite_extension_map : DPFusion.map composite_carrier [set: S]%G :=
  DPFusion.compose (preimage_map (extension_map a) (carrier b)) (extension_map b).

Lemma composite_extension_allowed : DPFusionSystem.allowed F composite_extension_map.
Proof.
apply: DPFusionSystem.composition_closed (extension_allowed b).
exact: preimage_map_allowed (extension_allowed a).
Qed.

Lemma composite_on_acting x : x \in P -> composite_extension_map x = DPFusion.compose f g x.
Proof.
move=> hx; have hv := subsetP composite_acting_sub _ hx.
rewrite /composite_extension_map (compose_in _ _ hv) (preimage_mapE hv).
rewrite (on_acting a hx) (on_acting b (map_into f hx)); exact: esym (compose_in f g hx).
Qed.

Lemma composite_entry_images i :
  map_morphism composite_extension_map @*
    subgroup c (index (DPNormalizerChainIndices.compose (indices a) (indices b)) i) = subgroup t i.
Proof.
rewrite compose_index; apply/setP=> y; apply/morphimP/idP.
- move=> [x hv hx ->]; rewrite map_morphismE /composite_extension_map compose_in // preimage_mapE //.
  have ha := subsetP (preimage_sub (extension_map a) (carrier b)) _ hv.
  have hd : extension_map a x \in subgroup d (index (indices b) i).
    rewrite -(entry_images a _); exact: mem_morphim ha hx.
  rewrite -(entry_images b i).
  exact: mem_morphim (subsetP (entry_sub_carrier b i) _ hd) hd.
- move=> hy; rewrite -(entry_images b i) in hy.
  have /morphimP[z hz hzd ey] := hy.
  rewrite map_morphismE in ey.
  rewrite -(entry_images a (index (indices b) i)) in hzd.
  have /morphimP[x hx hxc ez] := hzd.
  rewrite map_morphismE in ez.
  have hv : x \in composite_carrier.
    rewrite preimage_mem; apply/andP; split=> //.
    by rewrite -ez.
  exists x=> //.
  rewrite map_morphismE /composite_extension_map compose_in // preimage_mapE //.
  by rewrite -ez.
Qed.

Definition compose_extension : extension c t (DPFusion.compose f g) :=
  @Build_extension c t P U (DPFusion.compose f g)
    (DPNormalizerChainIndices.compose (indices a) (indices b)) composite_carrier
    composite_acting_sub composite_chain_sub composite_extension_map
    composite_extension_allowed composite_on_acting composite_entry_images.

End Extensions.
End DPNormalizerChainExtensions.
