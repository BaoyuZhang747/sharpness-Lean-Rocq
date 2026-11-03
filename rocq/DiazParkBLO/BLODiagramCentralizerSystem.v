(** The centraliser linking system is constructed from the supplied L.
    Its homs are actual linking morphisms fixing E, and every structural
    axiom is inherited through the proved subgroup and centre bijections. *)
From mathcomp Require Import all_boot all_fingroup center abelian pgroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation
  FusionOrbit FusionCentralizerMaps FusionCentralizer FusionCentralizerAmbient
  FusionCentralizerCoverProjection FusionCentralizerCoverFiberRaw.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem LinkingSystemFinite.
From DiazParkBLO Require Import BLODiagram BLODiagramCentralizerBase BLODiagramCenterElements.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionSubgroup DPFusionOrbit DPLinkingTransporter
  DPFusionCentralizerCoverProjection DPBLODiagram DPBLOCentralizerBase DPBLOCenterElements.
Local Open Scope group_scope.

Module DPBLOCentralizerSystem.
Section System.
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
Local Notation co := (@centralizer_point S F p pS sat B).
Local Notation ao := (@ambient_object S F p pS sat B).
Local Notation ch := (@centralizer_hom S F L p pS sat B).
Let cp (P Q : Obj) (f : ch P Q) := @centralizer_projection S F L p pS sat B P Q f.
Let ct (P Q : Obj) (s : transporter_hom (val P) (val Q)) :=
  @centralizer_transporter S F L p pS sat B P Q s.
Arguments cp P Q f : clear implicits.
Arguments ct P Q s : clear implicits.

Lemma centralizer_distinguished_underlying (P : Obj) (x : [subg (val P)]) :
    underlying_hom (ct P P (transporter_distinguished x)) =
    @DPCentricLinking.distinguished S F L (ao P) (subgroup_up x).
Proof.
change (@DPCentricLinking.linking_transporter S F L (ao P) (ao P)
  (@ambient_transporter S F p pS sat B P P (transporter_distinguished x)) =
  @DPCentricLinking.linking_transporter S F L (ao P) (ao P) (transporter_distinguished (subgroup_up x))).
f_equal; apply val_inj; reflexivity.
Qed.

Lemma centralizer_distinguished_injective (P : Obj) :
    injective (fun x : [subg (val P)] => ct P P (transporter_distinguished x)).
Proof.
move=> x y h.
have h0 := congr1 (@underlying_hom S F L E (co P) (co P)) h.
have h1 := eq_trans (esym (centralizer_distinguished_underlying x))
  (eq_trans h0 (centralizer_distinguished_underlying y)).
have hu := @DPCentricLinking.distinguished_injective S F L (ao P) (subgroup_up x) (subgroup_up y) h1.
exact: (can_inj (@subgroup_upK S C (val P))) hu.
Qed.

Lemma centralizer_projection_surjective (P Q : Obj) (f : DPFusionSystem.arrow CF (val P) (val Q)) :
    exists g : ch P Q, cp P Q g = f.
Proof.
pose a : DPFusionSystem.arrow F (val (ao P)) (val (ao Q)) :=
  Sub (DPFusionSubgroup.lift (val f)) (DPFusionCentralizerAmbient.lift_allowed (valP f)).
pose g := @DPLinkingFinite.chosen_lift S F L (ao P) (ao Q) a.
have hg : DPCentricLinking.linking_projection L g = a :=
  @DPLinkingFinite.chosen_lift_projection S F L (ao P) (ao Q) a.
have hf : DPFusionSystem.arrow_compose (alpha_to_carrier (co P))
    (DPCentricLinking.linking_projection L g) = alpha_to_carrier (co Q).
  apply DPFusionSystem.arrow_ext=> x hx.
  rewrite DPFusion.compose_in // !alpha_to_carrierE // !centralizer_point_alphaE // hg.
  rewrite (@alpha_to_carrierE S F E (co Q) x hx)
    (@centralizer_point_alphaE S F p pS sat B Q x hx).
  change (DPFusionSubgroup.lift (val f) x = x).
  exact: (@DPFusionCentralizerCoverFiberRaw.lift_fixes S F p B P Q f x hx).
pose gh : ch P Q := @Arrow S F L E (co P) (co Q) g hf.
exists gh; apply DPFusionSystem.arrow_ext=> x hx; apply val_inj.
rewrite centralizer_projectionE //.
change (val (DPCentricLinking.linking_projection L g) (val x) = val (val f x)).
rewrite hg; exact: DPFusionSubgroup.liftE hx.
Qed.

Lemma centralizer_central_action_underlying (P Q : Obj)
    (z : [subg 'Z(val P)]) (f : ch P Q) :
    underlying_hom (enlarged_compose (ct P P (transporter_distinguished (DPCentricLinking.center_element z))) f) =
    DPCentricLinking.linking_compose L
      (@DPCentricLinking.distinguished S F L (ao P) (DPCentricLinking.center_element (centre_up z)))
      (underlying_hom f).
Proof.
change (DPCentricLinking.linking_compose L
  (underlying_hom (ct P P (transporter_distinguished (DPCentricLinking.center_element z)))) (underlying_hom f) =
  DPCentricLinking.linking_compose L
    (@DPCentricLinking.distinguished S F L (ao P) (DPCentricLinking.center_element (centre_up z)))
    (underlying_hom f)).
by rewrite centralizer_distinguished_underlying centre_up_inclusion.
Qed.

Lemma centralizer_central_fiber (P Q : Obj) (f g : ch P Q) :
    cp P Q f = cp P Q g <->
    exists! z : [subg 'Z(val P)],
      enlarged_compose (ct P P (transporter_distinguished (DPCentricLinking.center_element z))) f = g.
Proof.
rewrite centralizer_projection_equal.
split.
- move=> h.
  have [z [hz hu]] := proj1 (@DPCentricLinking.central_fiber S F L (ao P) (ao Q)
    (underlying_hom f) (underlying_hom g)) h.
  exists (centre_down z); split.
  + apply enlarged_hom_ext; rewrite centralizer_central_action_underlying centre_downK; exact hz.
  + move=> w hw.
    apply (can_inj (@centre_upK S C (val P))).
    rewrite centre_downK.
    apply hu.
    have hh := congr1 (@underlying_hom S F L E (co P) (co Q)) hw.
    exact (eq_trans (esym (centralizer_central_action_underlying w f)) hh).
- move=> [z [hz _]].
  apply (proj2 (@DPCentricLinking.central_fiber S F L (ao P) (ao Q)
    (underlying_hom f) (underlying_hom g))).
  have h : DPCentricLinking.linking_compose L
      (@DPCentricLinking.distinguished S F L (ao P) (DPCentricLinking.center_element (centre_up z))) (underlying_hom f) = underlying_hom g.
    have hh := congr1 (@underlying_hom S F L E (co P) (co Q)) hz.
    exact (eq_trans (esym (centralizer_central_action_underlying z f)) hh).
  exists (centre_up z); split=> //.
  move=> w hw.
  (* Freeness is inherited from the actual ambient linking-system fibre. *)
  have hp : DPCentricLinking.linking_projection L (underlying_hom f) =
      DPCentricLinking.linking_projection L (underlying_hom g).
    rewrite -h DPCentricLinking.projection_compose.
    have hdelta : DPCentricLinking.linking_projection L
        (@DPCentricLinking.distinguished S F L (ao P) (DPCentricLinking.center_element (centre_up z))) =
        DPFusionSystem.arrow_identity F (val (ao P)).
      apply DPFusionSystem.arrow_ext=> x hx.
      rewrite /DPCentricLinking.distinguished DPCentricLinking.projection_transporter /=
        DPFusion.conjugation_in // DPFusion.identity_in //.
      apply/conjg_fixP/commgP.
      exact: esym (centP (setIP (valP (centre_up z))).2 x hx).
    rewrite hdelta; symmetry.
    exact (@compose_id_left (DPFusionSystem.fusion_category F) (val (ao P)) (val (ao Q))
      (DPCentricLinking.linking_projection L (underlying_hom f))).
  have [a [ha hau]] := proj1 (@DPCentricLinking.central_fiber S F L (ao P) (ao Q)
    (underlying_hom f) (underlying_hom g)) hp.
  exact (eq_trans (esym (hau (centre_up z) h)) (hau w hw)).
Qed.

Lemma centralizer_arrow_element (P Q : Obj) (f : ch P Q) (x : [subg (val P)]) :
    subgroup_up (DPCentricLinking.arrow_element (cp P Q f) x) =
    DPCentricLinking.arrow_element (DPCentricLinking.linking_projection L (underlying_hom f)) (subgroup_up x).
Proof.
apply val_inj; exact: (centralizer_projectionE f (valP x)).
Qed.

Lemma centralizer_commutation (P Q : Obj) (f : ch P Q) (x : [subg (val P)]) :
    enlarged_compose (ct P P (transporter_distinguished x)) f =
    enlarged_compose f (ct Q Q (transporter_distinguished (DPCentricLinking.arrow_element (cp P Q f) x))).
Proof.
apply enlarged_hom_ext.
change (DPCentricLinking.linking_compose L (underlying_hom (ct P P (transporter_distinguished x))) (underlying_hom f) =
  DPCentricLinking.linking_compose L (underlying_hom f)
    (underlying_hom (ct Q Q (transporter_distinguished (DPCentricLinking.arrow_element (cp P Q f) x))))).
rewrite !centralizer_distinguished_underlying centralizer_arrow_element.
exact: DPCentricLinking.commutation.
Qed.

Definition centralizer_linking_system : DPCentricLinking.system CF.
Proof.
refine {| DPCentricLinking.linking_hom := ch;
  DPCentricLinking.linking_identity := fun P => enlarged_identity L (co P);
  DPCentricLinking.linking_compose := fun P Q R f g => enlarged_compose f g;
  DPCentricLinking.linking_projection := cp;
  DPCentricLinking.linking_transporter := ct |}.
- move=> P Q f; exact (@compose_id_left (enlarged_category L E) (co P) (co Q) f).
- move=> P Q f; exact (@compose_id_right (enlarged_category L E) (co P) (co Q) f).
- move=> P Q R U f g h; exact (@Category.compose_assoc (enlarged_category L E) (co P) (co Q) (co R) (co U) f g h).
- exact: centralizer_projection_identity.
- exact: centralizer_projection_compose.
- exact: centralizer_transporter_identity.
- exact: centralizer_transporter_compose.
- exact: centralizer_projection_transporter.
- exact: centralizer_distinguished_injective.
- exact: centralizer_projection_surjective.
- exact: centralizer_central_fiber.
- exact: centralizer_commutation.
Defined.

Definition centralizer_inclusion : functor (DPCentricLinking.linking_category centralizer_linking_system)
    (enlarged_category L E).
Proof.
refine (@Build_functor (DPCentricLinking.linking_category centralizer_linking_system)
  (enlarged_category L E) co (fun P Q f => f) _ _); reflexivity.
Defined.

Lemma centralizer_inclusion_object P : fobj centralizer_inclusion P = co P.
Proof. reflexivity. Qed.
Lemma centralizer_inclusion_arrow P Q (f : DPCentricLinking.linking_hom centralizer_linking_system P Q) :
    fmap centralizer_inclusion f = f.
Proof. reflexivity. Qed.
End System.
End DPBLOCentralizerSystem.
