(** Native subgroup preimages and fusion restrictions for composing actual
    simultaneous extensions. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionMaps FusionSystems.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion.
Local Open Scope group_scope.

Module DPNormalizerChainExtensionPreimages.
Section Preimages.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.
Variable R : {group S}.

Definition preimage : {group S} := (map_morphism f @*^-1 R)%G.

Lemma preimage_sub : preimage \subset P.
Proof. exact: morphpre_sub. Qed.

Lemma preimage_mem x : (x \in preimage) = (x \in P) && (f x \in R).
Proof. by rewrite /preimage !inE. Qed.

Lemma preimage_restriction_image : image (restrict f preimage_sub) \subset R.
Proof.
apply/subsetP=> y /morphimP[x _ hx ->].
rewrite map_morphismE restrict_in //.
by move: hx; rewrite preimage_mem; move/andP=> [_].
Qed.

Definition preimage_map : DPFusion.map preimage R := corestrict preimage_restriction_image.

Lemma preimage_mapE x : x \in preimage -> preimage_map x = f x.
Proof. move=> hx; by rewrite /preimage_map corestrict_in // restrict_in. Qed.

Lemma preimage_map_allowed :
  DPFusionSystem.allowed F f -> DPFusionSystem.allowed F preimage_map.
Proof.
move=> hf; apply: DPFusionSystem.corestriction_allowed.
exact: DPFusionSystem.restriction_allowed hf.
Qed.

End Preimages.
End DPNormalizerChainExtensionPreimages.
