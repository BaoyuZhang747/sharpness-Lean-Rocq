(** The literal centraliser objects, linking arrows and their projections.
    The subgroup-type dictionary is the same one used by the accepted E3
    centraliser fibre; linking morphisms themselves are never quotiented. *)
From mathcomp Require Import all_boot all_fingroup center abelian pgroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation
  FusionOrbit FusionCentralizerMaps FusionCentralizer FusionCentralizerAmbient
  FusionCentralizerCover FusionCentralizerCoverProjection
  FusionCentralizerCoverFiberObjects FusionCentralizerCoverFiberRaw.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem.
From DiazParkBLO Require Import BLODiagram.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionSubgroup DPFusionOrbit DPLinkingTransporter
  DPFusionCentralizerCoverProjection DPBLODiagram.
Local Open Scope group_scope.

Module DPBLOCentralizerBase.
Section Centralizer.
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
Local Notation Obj := (centric_object CF).

Definition ambient_object (P : Obj) : centric_object F :=
  Sub (ambient (val P)) (@DPFusionCentralizerCoverFiberObjects.ambient_centric S F p pS sat B P).

Definition centralizer_point (P : Obj) : enlarged_object F E :=
  @Point S F E (ambient_object P)
    (Sub (DPFusion.inclusion (@DPFusionCentralizerCoverFiberObjects.ambient_center S F p B P))
      (DPFusionSystem.inclusion_allowed F
        (@DPFusionCentralizerCoverFiberObjects.ambient_center S F p B P))).

Lemma centralizer_point_alphaE (P : Obj) x (hx : x \in E) :
    val (alpha (centralizer_point P)) x = x.
Proof. exact: DPFusion.inclusion_in. Qed.

Definition centralizer_hom (P Q : Obj) :=
  enlarged_hom L (centralizer_point P) (centralizer_point Q).

Lemma centralizer_hom_fixes P Q (f : centralizer_hom P Q) :
    {in E, val (DPCentricLinking.linking_projection L (underlying_hom f)) =1 id}.
Proof.
move=> x hx; have h := commutesE f hx.
by rewrite !centralizer_point_alphaE // in h.
Qed.

Definition centralizer_projection P Q (f : centralizer_hom P Q) :
    DPFusionSystem.arrow CF (val P) (val Q) :=
  Sub (DPFusionSubgroup.lower (val (DPCentricLinking.linking_projection L (underlying_hom f))))
    (@DPFusionCentralizerCoverFiberRaw.lower_allowed_of_fixes S F p B P Q _
      (valP (DPCentricLinking.linking_projection L (underlying_hom f))) (centralizer_hom_fixes f)).

Lemma centralizer_projectionE P Q (f : centralizer_hom P Q) x (hx : x \in val P) :
    val (val (centralizer_projection f) x) =
    val (DPCentricLinking.linking_projection L (underlying_hom f)) (val x).
Proof. exact: DPFusionSubgroup.lowerE. Qed.

Lemma centralizer_projection_identity P :
    centralizer_projection (enlarged_identity L (centralizer_point P)) =
    DPFusionSystem.arrow_identity CF (val P).
Proof.
apply DPFusionSystem.arrow_ext=> x hx; apply val_inj.
rewrite centralizer_projectionE //.
change (val (DPCentricLinking.linking_projection L
  (DPCentricLinking.linking_identity L (ambient_object P))) (val x) =
  val (DPFusion.identity (val P) x)).
rewrite DPCentricLinking.projection_identity /= !DPFusion.identity_in //.
exact: ambient_mem hx.
Qed.

Lemma centralizer_projection_compose P Q R (f : centralizer_hom P Q) (g : centralizer_hom Q R) :
    centralizer_projection (enlarged_compose f g) =
    DPFusionSystem.arrow_compose (centralizer_projection f) (centralizer_projection g).
Proof.
apply DPFusionSystem.arrow_ext=> x hx; apply val_inj.
rewrite centralizer_projectionE // DPFusion.compose_in //.
rewrite centralizer_projectionE ?DPFusion.map_into // centralizer_projectionE //.
change (val (DPCentricLinking.linking_projection L
  (DPCentricLinking.linking_compose L (underlying_hom f) (underlying_hom g))) (val x) =
  val (DPCentricLinking.linking_projection L (underlying_hom g))
    (val (DPCentricLinking.linking_projection L (underlying_hom f)) (val x))).
rewrite DPCentricLinking.projection_compose /= DPFusion.compose_in //.
exact: ambient_mem hx.
Qed.

Lemma centralizer_projection_lift P Q (f : centralizer_hom P Q) :
    DPFusionSubgroup.lift (val (centralizer_projection f)) =
    val (DPCentricLinking.linking_projection L (underlying_hom f)).
Proof. exact: DPFusionCentralizerCoverFiberRaw.lift_lower. Qed.

Lemma centralizer_projection_equal P Q (f g : centralizer_hom P Q) :
    centralizer_projection f = centralizer_projection g <->
    DPCentricLinking.linking_projection L (underlying_hom f) =
    DPCentricLinking.linking_projection L (underlying_hom g).
Proof.
split.
- move=> h; apply val_inj.
  by rewrite -(centralizer_projection_lift f) -(centralizer_projection_lift g) h.
- move=> h; apply val_inj.
  change (DPFusionSubgroup.lower (val (DPCentricLinking.linking_projection L (underlying_hom f))) =
    DPFusionSubgroup.lower (val (DPCentricLinking.linking_projection L (underlying_hom g)))).
  by rewrite h.
Qed.

Lemma ambient_transporter_mem (P Q : Obj) (s : transporter_hom (val P) (val Q)) :
    ambient (val P) :^ (val (val s)) \subset ambient (val Q).
Proof.
apply/subsetP=> _ /imsetP[x /morphimP[y _ hy ->] ->].
change (val (y ^ val s) \in ambient (val Q)).
apply ambient_mem; apply (subsetP (valP s)); by rewrite memJ_conjg.
Qed.

Definition ambient_transporter (P Q : Obj) (s : transporter_hom (val P) (val Q)) :
    transporter_hom (val (ambient_object P)) (val (ambient_object Q)) :=
  Sub (val (val s)) (ambient_transporter_mem s).

Lemma ambient_transporter_identity (P : Obj) :
    ambient_transporter (transporter_identity (val P)) =
    transporter_identity (val (ambient_object P)).
Proof. apply val_inj; reflexivity. Qed.

Lemma ambient_transporter_compose (P Q R : Obj)
    (s : transporter_hom (val P) (val Q)) (t : transporter_hom (val Q) (val R)) :
    ambient_transporter (transporter_compose s t) =
    transporter_compose (ambient_transporter s) (ambient_transporter t).
Proof. apply val_inj; reflexivity. Qed.

Definition centralizer_transporter (P Q : Obj) (s : transporter_hom (val P) (val Q)) :
    centralizer_hom P Q.
Proof.
refine (@Arrow S F L E (centralizer_point P) (centralizer_point Q)
  (DPCentricLinking.linking_transporter L (ambient_transporter s)) _).
apply DPFusionSystem.arrow_ext=> x hx.
rewrite DPFusion.compose_in // !alpha_to_carrierE // !centralizer_point_alphaE //.
rewrite DPCentricLinking.projection_transporter /= DPFusion.conjugation_in.
- by rewrite conjgE -(centP (valP (val s)) x hx) mulKg.
- exact: (subsetP (@DPFusionCentralizerCoverFiberObjects.ambient_contains S F p B P) x hx).
Defined.

Lemma centralizer_transporter_identity (P : Obj) :
    centralizer_transporter (transporter_identity (val P)) =
    enlarged_identity L (centralizer_point P).
Proof.
apply enlarged_hom_ext.
change (DPCentricLinking.linking_transporter L (ambient_transporter (transporter_identity (val P))) =
  DPCentricLinking.linking_identity L (ambient_object P)).
rewrite ambient_transporter_identity; exact: DPCentricLinking.transporter_identity.
Qed.

Lemma centralizer_transporter_compose (P Q R : Obj)
    (s : transporter_hom (val P) (val Q)) (t : transporter_hom (val Q) (val R)) :
    centralizer_transporter (transporter_compose s t) =
    enlarged_compose (centralizer_transporter s) (centralizer_transporter t).
Proof.
apply enlarged_hom_ext.
change (DPCentricLinking.linking_transporter L (ambient_transporter (transporter_compose s t)) =
  DPCentricLinking.linking_compose L
    (DPCentricLinking.linking_transporter L (ambient_transporter s))
    (DPCentricLinking.linking_transporter L (ambient_transporter t))).
rewrite ambient_transporter_compose; exact: DPCentricLinking.transporter_compose.
Qed.

Lemma centralizer_projection_transporter (P Q : Obj) (s : transporter_hom (val P) (val Q)) :
    centralizer_projection (centralizer_transporter s) = transporter_arrow CF s.
Proof.
apply DPFusionSystem.arrow_ext=> x hx; apply val_inj.
rewrite centralizer_projectionE //.
change (val (DPCentricLinking.linking_projection L
  (DPCentricLinking.linking_transporter L (ambient_transporter s))) (val x) =
  val (DPFusion.conjugation (valP s) x)).
rewrite DPCentricLinking.projection_transporter /= !DPFusion.conjugation_in //.
exact: ambient_mem hx.
Qed.
End Centralizer.
End DPBLOCentralizerBase.
