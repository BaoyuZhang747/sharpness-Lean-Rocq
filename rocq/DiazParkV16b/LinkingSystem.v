(** A centric linking system with its standard structural axioms only.
    Objects are literally the existing F-centric subgroups.  Morphisms are
    arbitrary types: finiteness, cancellation, and restriction lifting are
    consequences to be proved, not fields of this definition. *)
From mathcomp Require Import all_boot all_fingroup center.
From DiazPark Require Import Category CategoryReindex FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystemTransporter.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter.
Local Open Scope group_scope.

Module DPCentricLinking.
Section StructuralData.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition center_element (P : {group S}) (z : [subg 'Z(P)]) : [subg P] :=
  Sub (val z) (subsetP (center_sub P) _ (valP z)).

Definition arrow_element (P Q : {group S}) (f : DPFusionSystem.arrow F P Q)
    (x : [subg P]) : [subg Q] :=
  Sub (DPFusion.map_fun (val f) (val x)) (DPFusion.map_into (val f) (valP x)).

Record system := LinkingSystem {
  linking_hom : Obj -> Obj -> Type;
  linking_identity : forall P, linking_hom P P;
  linking_compose : forall {P Q R}, linking_hom P Q -> linking_hom Q R -> linking_hom P R;
  linking_id_left : forall P Q (f : linking_hom P Q), linking_compose (linking_identity P) f = f;
  linking_id_right : forall P Q (f : linking_hom P Q), linking_compose f (linking_identity Q) = f;
  linking_assoc : forall P Q R T (f : linking_hom P Q) (g : linking_hom Q R)
    (h : linking_hom R T), linking_compose (linking_compose f g) h = linking_compose f (linking_compose g h);
  linking_projection : forall {P Q}, linking_hom P Q -> DPFusionSystem.arrow F (val P) (val Q);
  projection_identity : forall P, linking_projection (linking_identity P) = DPFusionSystem.arrow_identity F (val P);
  projection_compose : forall P Q R (f : linking_hom P Q) (g : linking_hom Q R),
    linking_projection (linking_compose f g) =
      DPFusionSystem.arrow_compose (linking_projection f) (linking_projection g);
  linking_transporter : forall {P Q}, transporter_hom (val P) (val Q) -> linking_hom P Q;
  transporter_identity : forall P,
    linking_transporter (DPLinkingTransporter.transporter_identity (val P)) = linking_identity P;
  transporter_compose : forall P Q R (s : transporter_hom (val P) (val Q))
      (t : transporter_hom (val Q) (val R)),
    linking_transporter (DPLinkingTransporter.transporter_compose s t) =
      linking_compose (linking_transporter s) (linking_transporter t);
  projection_transporter : forall P Q (s : transporter_hom (val P) (val Q)),
    linking_projection (linking_transporter s) = transporter_arrow F s;
  distinguished_injective : forall P,
    injective (fun x : [subg (val P)] =>
      @linking_transporter P P (transporter_distinguished x));
  projection_surjective : forall P Q (f : DPFusionSystem.arrow F (val P) (val Q)),
    exists g : linking_hom P Q, linking_projection g = f;
  central_fiber : forall P Q (f g : linking_hom P Q),
    linking_projection f = linking_projection g <->
    exists! z : [subg 'Z(val P)],
      linking_compose (linking_transporter (transporter_distinguished (center_element z))) f = g;
  commutation : forall P Q (f : linking_hom P Q) (x : [subg (val P)]),
    linking_compose (linking_transporter (transporter_distinguished x)) f =
    linking_compose f (linking_transporter (transporter_distinguished (arrow_element (linking_projection f) x)))
}.
End StructuralData.

Arguments linking_hom {S F} _ _ _.
Arguments linking_identity {S F} _ _.
Arguments linking_compose {S F} _ {P Q R} _ _.
Arguments linking_projection {S F} _ {P Q} _.
Arguments linking_transporter {S F} _ {P Q} _.

Section Categories.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : system F.
Local Notation Obj := (DPFusionOrbit.centric_object F).

Definition linking_category : category :=
  @Build_category Obj (linking_hom L) (linking_identity L) (@linking_compose _ _ L)
    (@linking_id_left _ _ L) (@linking_id_right _ _ L) (@linking_assoc _ _ L).

Definition projection : functor linking_category (centric_fusion_category F).
Proof.
refine (@Build_functor linking_category (centric_fusion_category F)
  (fun P => P) (fun P Q f => linking_projection L f) _ _).
- exact: projection_identity.
- exact: projection_compose.
Defined.

Definition raw_projection : functor linking_category (DPFusionSystem.fusion_category F) :=
  functor_comp projection (centric_fusion_inclusion F).

Definition transporter : functor (centric_transporter_category F) linking_category.
Proof.
refine (@Build_functor (centric_transporter_category F) linking_category
  (fun P => P) (fun P Q s => linking_transporter L s) _ _).
- exact: transporter_identity.
- exact: transporter_compose.
Defined.

Lemma projection_object (P : Obj) : fobj projection P = P.
Proof. reflexivity. Qed.
Lemma raw_projection_object (P : Obj) : fobj raw_projection P = val P.
Proof. reflexivity. Qed.
Lemma transporter_object (P : Obj) : fobj transporter P = P.
Proof. reflexivity. Qed.

Definition distinguished (P : Obj) (x : [subg (val P)]) : hom linking_category P P :=
  linking_transporter L (transporter_distinguished x).

Lemma distinguished_one (P : Obj) : distinguished (1 : [subg (val P)]) = @identity linking_category P.
Proof.
rewrite /distinguished transporter_distinguished_one; exact: transporter_identity.
Qed.

Lemma distinguished_mul (P : Obj) (x y : [subg (val P)]) :
    distinguished (x * y) = @compose linking_category P P P (distinguished x) (distinguished y).
Proof.
rewrite /distinguished transporter_distinguished_mul; exact: transporter_compose.
Qed.

Definition distinguished_isomorphism (P : Obj) (x : [subg (val P)]) :
    @isomorphism linking_category P P.
Proof.
refine (@Build_isomorphism linking_category P P (distinguished x) (distinguished x^-1) _ _).
- by rewrite -distinguished_mul mulgV distinguished_one.
- by rewrite -distinguished_mul mulVg distinguished_one.
Defined.

Definition inclusion (P Q : Obj) (hPQ : val P \subset val Q) : hom linking_category P Q :=
  linking_transporter L (transporter_inclusion hPQ).

Lemma inclusion_identity (P : Obj) : inclusion (subxx (val P)) = @identity linking_category P.
Proof.
have he : transporter_inclusion (subxx (val P)) = DPLinkingTransporter.transporter_identity (val P).
  apply val_inj; reflexivity.
rewrite /inclusion he; exact: transporter_identity.
Qed.

Lemma inclusion_compose (P Q R : Obj) (hPQ : val P \subset val Q) (hQR : val Q \subset val R) :
    @compose linking_category P Q R (inclusion hPQ) (inclusion hQR) = inclusion (subset_trans hPQ hQR).
Proof.
change (linking_compose L (linking_transporter L (transporter_inclusion hPQ))
  (linking_transporter L (transporter_inclusion hQR)) =
  linking_transporter L (transporter_inclusion (subset_trans hPQ hQR))).
rewrite -transporter_compose transporter_inclusion_compose; reflexivity.
Qed.

Lemma projection_inclusion (P Q : Obj) (hPQ : val P \subset val Q) :
    val (fmap projection (inclusion hPQ)) = DPFusion.inclusion hPQ.
Proof.
change (val (linking_projection L (linking_transporter L (transporter_inclusion hPQ))) =
  DPFusion.inclusion hPQ).
rewrite projection_transporter; apply DPFusion.map_ext => x Px.
by rewrite DPFusion.conjugation_in // DPFusion.inclusion_in // conjg1.
Qed.
End Categories.
End DPCentricLinking.

Check DPCentricLinking.system.
Check DPCentricLinking.linking_category.
Check DPCentricLinking.raw_projection.
Check DPCentricLinking.transporter.
Check DPCentricLinking.central_fiber.
Print Assumptions DPCentricLinking.inclusion_compose.
