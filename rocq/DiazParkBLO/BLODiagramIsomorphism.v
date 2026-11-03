(** Lifting an actual underlying linking isomorphism to the enlarged
    category when its forward arrow obeys the defining square. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem.
From DiazParkBLO Require Import BLODiagram.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPBLODiagram.

Module DPBLODiagramIsomorphism.
Section Isomorphism.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable E : {group S}.
Variables X Y : enlarged_object F E.
Variable f : enlarged_hom L X Y.
Variable e : @isomorphism (DPCentricLinking.linking_category L) (underlying X) (underlying Y).
Hypothesis he : iso_hom e = underlying_hom f.

Definition enlarged_inverse : enlarged_hom L Y X.
Proof.
refine (@Arrow S F L E Y X (iso_inv e) _).
rewrite -(commutes f) arrow_associativity.
have h : DPFusionSystem.arrow_compose
    (DPCentricLinking.linking_projection L (underlying_hom f))
    (DPCentricLinking.linking_projection L (iso_inv e)) =
    DPFusionSystem.arrow_identity F (val (underlying X)).
  rewrite -DPCentricLinking.projection_compose -he.
  change (DPCentricLinking.linking_projection L (Category.compose (iso_hom e) (iso_inv e)) =
    DPFusionSystem.arrow_identity F (val (underlying X))).
  by rewrite iso_hom_inv DPCentricLinking.projection_identity.
rewrite h.
exact (@compose_id_right (DPFusionSystem.fusion_category F) E (val (underlying X)) (alpha_to_carrier X)).
Defined.

Definition enlarged_isomorphism : @isomorphism (enlarged_category L E) X Y.
Proof.
refine (@Build_isomorphism (enlarged_category L E) X Y f enlarged_inverse _ _).
- apply enlarged_hom_ext.
  change (DPCentricLinking.linking_compose L (underlying_hom f) (iso_inv e) =
    DPCentricLinking.linking_identity L (underlying X)).
  rewrite -he; exact (iso_hom_inv e).
- apply enlarged_hom_ext.
  change (DPCentricLinking.linking_compose L (iso_inv e) (underlying_hom f) =
    DPCentricLinking.linking_identity L (underlying Y)).
  rewrite -he; exact (iso_inv_hom e).
Defined.

Lemma enlarged_isomorphism_hom : iso_hom enlarged_isomorphism = f.
Proof. reflexivity. Qed.
Lemma enlarged_isomorphism_inv : underlying_hom (iso_inv enlarged_isomorphism) = iso_inv e.
Proof. reflexivity. Qed.
End Isomorphism.
End DPBLODiagramIsomorphism.
