(** Finiteness is derived from the actual finite fusion morphism set and
    the linking system's central fibres.  No finite-Hom axiom is assumed. *)
From mathcomp Require Import all_boot all_fingroup center boolp.
From DiazPark Require Import Category CategoryFinite FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking.
Local Open Scope group_scope.

Module DPLinkingFinite.
Section FiniteMorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables P Q : DPFusionOrbit.centric_object F.

Definition chosen_lift (a : DPFusionSystem.arrow F (val P) (val Q)) : linking_hom L P Q :=
  proj1_sig (cid (@projection_surjective S F L P Q a)).

Lemma chosen_lift_projection (a : DPFusionSystem.arrow F (val P) (val Q)) :
    linking_projection L (chosen_lift a) = a.
Proof. exact: (proj2_sig (cid (@projection_surjective S F L P Q a))). Qed.

Lemma coordinate_exists (f : linking_hom L P Q) :
    exists z : [subg 'Z(val P)],
      linking_compose L (distinguished L (center_element z))
        (chosen_lift (linking_projection L f)) = f.
Proof.
have [z [hz _]] := proj1 (@central_fiber S F L P Q
  (chosen_lift (linking_projection L f)) f) (chosen_lift_projection _).
by exists z.
Qed.

Definition coordinate (f : linking_hom L P Q) : [subg 'Z(val P)] :=
  proj1_sig (cid (coordinate_exists f)).

Lemma coordinate_spec (f : linking_hom L P Q) :
    linking_compose L (distinguished L (center_element (coordinate f)))
      (chosen_lift (linking_projection L f)) = f.
Proof. exact: (proj2_sig (cid (coordinate_exists f))). Qed.

Definition coordinate_type : finType :=
  [the finType of (DPFusionSystem.arrow F (val P) (val Q) * [subg 'Z(val P)])%type].

Definition encode (f : linking_hom L P Q) : coordinate_type :=
  (linking_projection L f, coordinate f).

Definition decode (a : coordinate_type) : linking_hom L P Q :=
  linking_compose L (distinguished L (center_element a.2)) (chosen_lift a.1).

Lemma decode_encode : cancel encode decode.
Proof. exact: coordinate_spec. Qed.

(** can_type retains the original linking-Hom carrier and obtains its
    finite structure from the displayed injection into a genuine finType. *)
Definition hom_finType : finType := can_type decode_encode.

Lemma hom_finType_carrier : (hom_finType : Type) = linking_hom L P Q.
Proof. reflexivity. Qed.

Lemma hom_enum_complete (f : hom_finType) : f \in enum hom_finType.
Proof. exact: mem_enum. Qed.
End FiniteMorphisms.

Section FiniteCategory.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Definition linking_finite_category : finite_category.
Proof.
refine (@Build_finite_category [the finType of DPFusionOrbit.centric_object F]
  (hom_finType L) (linking_identity L) (@linking_compose _ _ L) _ _ _).
- exact: linking_id_left.
- exact: linking_id_right.
- exact: linking_assoc.
Defined.

Definition finite_to_linking : functor (fc_category linking_finite_category) (linking_category L).
Proof.
refine (@Build_functor (fc_category linking_finite_category) (linking_category L)
  (fun P => P) (fun P Q f => f) _ _); reflexivity.
Defined.

Definition linking_to_finite : functor (linking_category L) (fc_category linking_finite_category).
Proof.
refine (@Build_functor (linking_category L) (fc_category linking_finite_category)
  (fun P => P) (fun P Q f => f) _ _); reflexivity.
Defined.
End FiniteCategory.
End DPLinkingFinite.

Check DPLinkingFinite.hom_finType.
Check DPLinkingFinite.linking_finite_category.
Print Assumptions DPLinkingFinite.decode_encode.
Print Assumptions DPLinkingFinite.linking_finite_category.
