(** Actual simultaneous extensions that carry a normalized subgroup into
    another subgroup.  These are the arrows of the pointed enlargement. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems.
From DiazParkV16b Require Import NormalizerChainExtensionPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPNormalizerChainExtensionPreimages.
Local Open Scope group_scope.

Module DPNormalizerSubgroupExtensions.
Section Extensions.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Record extension (R T : {group S}) (P Q : {group S}) (f : DPFusion.map P Q) := {
  carrier : {group S};
  acting_sub : P \subset carrier;
  subgroup_sub : R \subset carrier;
  extension_map : DPFusion.map carrier [set: S]%G;
  extension_allowed : DPFusionSystem.allowed F extension_map;
  on_acting : forall x, x \in P -> extension_map x = f x;
  maps_into : forall x, x \in R -> extension_map x \in T
}.

Definition identity_extension (P R : {group S}) : extension R R (identity P).
Proof.
pose V := (P <*> R)%G.
refine (@Build_extension R R P P (identity P) V (joing_subl _ _) (joing_subr _ _)
  (inclusion (subsetT V)) (DPFusionSystem.inclusion_allowed F _) _ _).
- move=> x hx; by rewrite inclusion_in ?(subsetP (joing_subl P R) _ hx) // identity_in.
- move=> x hx; by rewrite inclusion_in ?(subsetP (joing_subr P R) _ hx).
Defined.

Section Composition.
Variables P Q U R T V : {group S}.
Variables f : DPFusion.map P Q.
Variables g : DPFusion.map Q U.
Variable a : extension R T f.
Variable b : extension T V g.

Definition composite_carrier := preimage (extension_map a) (carrier b).

Lemma composite_acting_sub : P \subset composite_carrier.
Proof.
apply/subsetP=> x hx; rewrite preimage_mem; apply/andP; split.
- exact: subsetP (acting_sub a) _ hx.
- rewrite (on_acting a hx); exact: subsetP (acting_sub b) _ (map_into f hx).
Qed.

Lemma composite_subgroup_sub : R \subset composite_carrier.
Proof.
apply/subsetP=> x hx; rewrite preimage_mem; apply/andP; split.
- exact: subsetP (subgroup_sub a) _ hx.
- exact: subsetP (subgroup_sub b) _ (maps_into a hx).
Qed.

Definition composite_map := compose (preimage_map (extension_map a) (carrier b)) (extension_map b).

Definition compose_extension : extension R V (compose f g).
Proof.
refine (@Build_extension R V P U (compose f g) composite_carrier
  composite_acting_sub composite_subgroup_sub composite_map _ _ _).
- apply: DPFusionSystem.composition_closed (extension_allowed b).
  exact: preimage_map_allowed (extension_allowed a).
- move=> x hx; have hv := subsetP composite_acting_sub _ hx.
  rewrite /composite_map (compose_in _ _ hv) (preimage_mapE hv).
  by rewrite (on_acting a hx) (on_acting b (map_into f hx)) compose_in.
- move=> x hx; have hv := subsetP composite_subgroup_sub _ hx.
  rewrite /composite_map (compose_in _ _ hv) (preimage_mapE hv).
  exact: maps_into (maps_into a hx).
Defined.
End Composition.

Section Join.
Variables P Q R T : {group S}.
Variable f : DPFusion.map P Q.
Variable a : extension R T f.

Lemma join_maps x : x \in P <*> R -> extension_map a x \in Q <*> T.
Proof.
have hs : P <*> R \subset preimage (extension_map a) (Q <*> T)%G.
  rewrite join_subG; apply/andP; split; apply/subsetP=> y hy;
    rewrite preimage_mem; apply/andP; split.
  - exact: subsetP (acting_sub a) _ hy.
  - rewrite (on_acting a hy); exact: subsetP (joing_subl Q T) _ (map_into f hy).
  - exact: subsetP (subgroup_sub a) _ hy.
  - exact: subsetP (joing_subr Q T) _ (maps_into a hy).
move=> hx; have h := subsetP hs _ hx; by rewrite preimage_mem in h; have /andP[_] := h.
Qed.

Definition join_extension : extension (P <*> R)%G (Q <*> T)%G f.
Proof.
refine (@Build_extension (P <*> R)%G (Q <*> T)%G P Q f
  (carrier a) (acting_sub a) _ (extension_map a) (extension_allowed a) (on_acting a) join_maps).
by rewrite join_subG (acting_sub a) (subgroup_sub a).
Defined.
End Join.
End Extensions.
End DPNormalizerSubgroupExtensions.
