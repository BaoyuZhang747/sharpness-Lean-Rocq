(** Inverting the actual full extension image gives a genuine inverse
    subgroup extension when the acting map is onto. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy.
From DiazParkV16b Require Import NormalizerPointedSubgroupExtensions NormalizerPointedSubgroupImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionConjugacy DPNormalizerSubgroupExtensions DPNormalizerSubgroupImages.
Local Open Scope group_scope.

Module DPNormalizerSubgroupImageInverse.
Section Inverse.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q R T : {group S}.
Variable f : DPFusion.map P Q.
Variable a : extension F R T f.
Hypothesis onto : image f = Q.

Lemma target_in_full_image : Q \subset image (extension_map a).
Proof.
rewrite -{1}onto -(acting_image a).
apply/subsetP=> y /morphimP[x hv hx ->].
exact: image_mem hv.
Qed.

Lemma subgroup_in_full_image : subgroup_image a \subset image (extension_map a).
Proof. apply/subsetP=> y /morphimP[x hv hx ->]; exact: image_mem hv. Qed.

Definition inverse_extension_map : DPFusion.map (image (extension_map a)) [set: S]%G :=
  compose (inverse (extension_map a)) (inclusion (subsetT (carrier a))).

Lemma inverse_extension_mapE x : x \in image (extension_map a) ->
  inverse_extension_map x = inverse (extension_map a) x.
Proof. move=> hx; by rewrite /inverse_extension_map compose_in // inclusion_in ?map_into. Qed.

Definition inverse_extension : extension F (subgroup_image a) R (onto_inverse onto).
Proof.
refine (@Build_extension S F (subgroup_image a) R Q P (onto_inverse onto)
  (image (extension_map a)) target_in_full_image subgroup_in_full_image inverse_extension_map _ _ _).
- apply: DPFusionSystem.composition_closed.
  + exact: DPFusionSystem.inverse_closed (extension_allowed a).
  + exact: DPFusionSystem.inclusion_allowed.
- move=> y hy.
  have him : y \in image f by rewrite onto.
  have /morphimP[x hx _ ey] := him; rewrite map_morphismE in ey.
  rewrite inverse_extension_mapE ?(subsetP target_in_full_image _ hy) // ey.
  rewrite -(on_acting a hx) inverse_cancel ?(subsetP (acting_sub a) _ hx) //.
  rewrite on_acting // onto_inverse_cancel //.
- move=> y hy; have /morphimP[x hv hx ey] := hy; rewrite map_morphismE in ey.
  rewrite inverse_extension_mapE; last exact: subsetP subgroup_in_full_image _ hy.
  by rewrite ey inverse_cancel.
Defined.
End Inverse.
End DPNormalizerSubgroupImageInverse.
