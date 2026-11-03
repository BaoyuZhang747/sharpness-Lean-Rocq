(** Every actual enlarged object is isomorphic to one in the centraliser
    linking category. The embedding is straightened by saturation, then
    lifted to an actual linking isomorphism. *)
From mathcomp Require Import all_boot all_fingroup center abelian pgroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation
  FusionSaturationImage FusionOrbit FusionCentricBasics FusionCentralizerMaps
  FusionCentralizer FusionCentralizerCentric FusionCentralizerCompression
  FusionAbelianCentralizerExtension FusionCentralizerCoverProjection
  FusionCentralizerCoverFiberObjects.
From DiazParkV16b Require Import LinkingSystem LinkingSystemFinite LinkingSystemIsomorphisms.
From DiazParkBLO Require Import BLODiagram BLODiagramIsomorphism BLODiagramCentralizerBase.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionSubgroup DPFusionOrbit DPFusionCentralizerCoverProjection
  DPBLODiagram DPBLOCentralizerBase DPBLODiagramIsomorphism.
Local Open Scope group_scope.

Module DPBLOCentralizerObjects.
Section EssentialSurjectivity.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.
Local Notation CF := (DPFusionCentralizer.system F E).
Variable X : enlarged_object F E.
Local Notation P := (val (underlying X)).
Local Notation A := (DPFusion.image (val (alpha X))).

Lemma alpha_image_abelian : abelian A.
Proof.
exact: morphim_abelian (@DPFusionCentralizerCoverFiberObjects.elementary_abelian S F p B).
Qed.

Lemma straightening_exists : exists g : DPFusion.map 'C(A)%G C,
    DPFusionSystem.allowed F g && [forall x in A, g x == DPFusion.inverse (val (alpha X)) x].
Proof.
have [g [hg he]] := DPFusionAbelianCentralizerExtension.centralizer_extension_exists
  sat (DPFusionSystem.inverse_closed (valP (alpha X)))
  (DPFusionCentralizerCompression.inverse_image (val (alpha X))) alpha_image_abelian
  (@DPFusionCentralizerCoverFiberObjects.elementary_centralized S F p B).
exists g; apply/andP; split=> //.
apply/forall_inP=> x hx; apply/eqP; exact: he hx.
Qed.

Definition straightening : DPFusion.map 'C(A)%G C := xchoose straightening_exists.
Lemma straightening_allowed : DPFusionSystem.allowed F straightening.
Proof. exact: (andP (xchooseP straightening_exists)).1. Qed.
Lemma straighteningE : {in A, straightening =1 DPFusion.inverse (val (alpha X))}.
Proof. move=> x hx; apply/eqP; exact: (forall_inP (andP (xchooseP straightening_exists)).2) x hx. Qed.

Lemma carrier_centralizes_image : P \subset 'C(A).
Proof.
apply: subset_trans (centS (DPFusion.image_sub (val (alpha X)))).
rewrite centsC; exact: subsetIr.
Qed.

Definition restricted_straightening := DPFusion.restrict straightening carrier_centralizes_image.
Lemma restricted_straightening_allowed : DPFusionSystem.allowed F restricted_straightening.
Proof. exact: DPFusionSystem.restriction_allowed straightening_allowed. Qed.

Definition target_group := DPFusion.image restricted_straightening.
Lemma target_group_centric : DPFusionSystem.centric F target_group.
Proof. exact: DPFusionCentricBasics.centric_image restricted_straightening_allowed (valP (underlying X)). Qed.
Lemma target_group_sub : target_group \subset C.
Proof. exact: DPFusion.image_sub. Qed.

Lemma straightening_alpha x (hx : x \in E) :
    restricted_straightening (val (alpha X) x) = x.
Proof.
have hp : val (alpha X) x \in P :=
  subsetP (center_sub P) _ (DPFusion.map_into (val (alpha X)) hx).
rewrite /restricted_straightening DPFusion.restrict_in // straighteningE ?DPFusion.image_mem //.
exact: DPFusion.inverse_cancel hx.
Qed.

Definition target_local_group : {group T} := (subg C @* target_group)%G.
Lemma target_local_ambient : ambient target_local_group = target_group.
Proof. apply val_inj; exact: subgmK target_group_sub. Qed.
Lemma target_local_centric : DPFusionSystem.centric CF target_local_group.
Proof.
apply: DPFusionCentralizerCentric.ambient_centric_centralizer_centric.
by rewrite target_local_ambient target_group_centric.
Qed.
Definition target_object : centric_object CF := Sub target_local_group target_local_centric.

Lemma target_projection_range :
    DPFusion.image restricted_straightening \subset ambient (val target_object).
Proof. by change (target_group \subset ambient target_local_group); rewrite target_local_ambient. Qed.

Definition target_projection : DPFusionSystem.arrow F P (ambient (val target_object)) :=
  Sub (DPFusion.corestrict target_projection_range)
    (DPFusionSystem.corestriction_allowed target_projection_range restricted_straightening_allowed).

Lemma target_projection_alpha x (hx : x \in E) : val target_projection (val (alpha X) x) = x.
Proof.
rewrite /target_projection /= DPFusion.corestrict_in.
- exact: straightening_alpha hx.
- exact: (subsetP (center_sub P) _ (DPFusion.map_into (val (alpha X)) hx)).
Qed.

Lemma target_projection_onto : DPFusion.image (val target_projection) = ambient (val target_object).
Proof. by rewrite /target_projection /= DPFusionSaturationImage.image_corestrict target_local_ambient. Qed.

Local Notation Y := (@centralizer_point S F p pS sat B target_object).

Definition straightening_link : DPCentricLinking.linking_hom L (underlying X) (underlying Y) :=
  @DPLinkingFinite.chosen_lift S F L (underlying X) (underlying Y) target_projection.

Lemma straightening_link_projection : DPCentricLinking.linking_projection L straightening_link = target_projection.
Proof. exact: DPLinkingFinite.chosen_lift_projection. Qed.

Definition straightening_arrow : enlarged_hom L X Y.
Proof.
refine (@Arrow S F L E X Y straightening_link _).
apply DPFusionSystem.arrow_ext=> x hx.
rewrite DPFusion.compose_in // !alpha_to_carrierE // straightening_link_projection.
by rewrite target_projection_alpha // centralizer_point_alphaE.
Defined.

Lemma straightening_link_onto :
    DPFusion.image (val (DPCentricLinking.linking_projection L straightening_link)) = val (underlying Y).
Proof. rewrite straightening_link_projection; exact: target_projection_onto. Qed.

Definition straightening_link_iso :
    @isomorphism (DPCentricLinking.linking_category L) (underlying X) (underlying Y) :=
  DPLinkingIsomorphisms.isomorphism_of_image_eq straightening_link_onto.

Definition straightening_iso : @isomorphism (enlarged_category L E) X Y :=
  @enlarged_isomorphism S F L E X Y straightening_arrow straightening_link_iso (Logic.eq_refl _).

Lemma straightening_iso_forward : underlying_hom (iso_hom straightening_iso) = straightening_link.
Proof. reflexivity. Qed.
End EssentialSurjectivity.
End DPBLOCentralizerObjects.
