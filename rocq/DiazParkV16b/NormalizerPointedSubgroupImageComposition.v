(** Literal image of a composite simultaneous extension. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems.
From DiazParkV16b Require Import NormalizerChainExtensionPreimages
  NormalizerPointedSubgroupExtensions NormalizerPointedSubgroupImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPNormalizerChainExtensionPreimages DPNormalizerSubgroupExtensions
  DPNormalizerSubgroupImages.
Local Open Scope group_scope.

Module DPNormalizerSubgroupImageComposition.
Section Composition.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q N R T U : {group S}.
Variable f : DPFusion.map P Q.
Variable g : DPFusion.map Q N.
Variable a : extension F R T f.
Variable b : extension F T U g.

Lemma image_of_composition :
  (subgroup_image (compose_extension a b) : {set S}) =
    map_morphism (extension_map b) @* subgroup_image a.
Proof.
apply/setP=> y; apply/morphimP/morphimP.
- move=> [x hv hx ->].
  change (morphism.morphim_spec (carrier b) (subgroup_image a)
    (composite_map a b x) (map_morphism (extension_map b))).
  have ha := subsetP (preimage_sub (extension_map a) (carrier b)) _ hv.
  have hb : extension_map a x \in carrier b :=
    subsetP (subgroup_sub b) _ (maps_into a hx).
  exists (extension_map a x)=> //; first exact: subgroup_image_mem hx.
  by rewrite map_morphismE /composite_map compose_in // preimage_mapE.
- move=> [z hz hzi ey]; rewrite map_morphismE in ey.
  have /morphimP[x hx hxr ex] := hzi; rewrite map_morphismE in ex.
  have hv : x \in composite_carrier a b.
    rewrite /composite_carrier preimage_mem; apply/andP; split=> //.
    by rewrite -ex.
  exists x=> //.
  rewrite map_morphismE /composite_map compose_in // preimage_mapE // -ex.
  exact ey.
Qed.
End Composition.
End DPNormalizerSubgroupImageComposition.
