(** Actual transporter and raw fusion categories for centric linking systems.
    MathComp uses x ^ s = s^-1 * x * s; transporter composition is s * t. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category CategoryReindex CategoryFinite
  FusionMaps FusionSystems FusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPLinkingTransporter.
Section Transporters.
Variable S : finGroupType.

Definition transporter_hom (P Q : {group S}) := {s : S | P :^ s \subset Q}.

Definition transporter_identity (P : {group S}) : transporter_hom P P.
Proof. apply: (Sub (1 : S)); by rewrite conjsg1. Defined.

Lemma transporter_compose_mem (P Q R : {group S})
    (s : transporter_hom P Q) (t : transporter_hom Q R) :
    P :^ (val s * val t) \subset R.
Proof.
apply/subsetP => z /imsetP[x Px ->]; rewrite conjgM.
apply: (subsetP (valP t)); apply/imsetP; exists (x ^ val s) => //.
apply: (subsetP (valP s)); apply/imsetP; by exists x.
Qed.

Definition transporter_compose (P Q R : {group S})
    (s : transporter_hom P Q) (t : transporter_hom Q R) : transporter_hom P R :=
  Sub (val s * val t) (transporter_compose_mem s t).

Definition transporter_category : category.
Proof.
refine (@Build_category {group S} transporter_hom transporter_identity
  (fun P Q R s t => @transporter_compose P Q R s t) _ _ _).
- move=> P Q s; apply val_inj; exact: mul1g.
- move=> P Q s; apply val_inj; exact: mulg1.
- move=> P Q R T s t u; apply val_inj; exact: esym (mulgA _ _ _).
Defined.

Definition transporter_inclusion (P Q : {group S}) (h : P \subset Q) :
    transporter_hom P Q.
Proof. apply: (Sub (1 : S)); by rewrite conjsg1. Defined.

Definition transporter_distinguished (P : {group S}) (x : [subg P]) : transporter_hom P P.
Proof.
apply: (Sub (val x)).
by rewrite (normP (subsetP (normG P) _ (valP x))).
Defined.

Lemma transporter_distinguished_one (P : {group S}) :
    transporter_distinguished (1 : [subg P]) = transporter_identity P.
Proof. apply val_inj; reflexivity. Qed.

Lemma transporter_distinguished_mul (P : {group S}) (x y : [subg P]) :
    transporter_distinguished (x * y) =
    transporter_compose (transporter_distinguished x) (transporter_distinguished y).
Proof. apply val_inj; reflexivity. Qed.

Lemma transporter_inclusion_compose (P Q R : {group S})
    (hPQ : P \subset Q) (hQR : Q \subset R) :
    transporter_compose (transporter_inclusion hPQ) (transporter_inclusion hQR) =
    transporter_inclusion (subset_trans hPQ hQR).
Proof. apply val_inj; exact: mulg1. Qed.

Variable F : DPFusionSystem.system S.

Definition transporter_arrow (P Q : {group S}) (s : transporter_hom P Q) :
    DPFusionSystem.arrow F P Q :=
  Sub (DPFusion.conjugation (valP s)) (DPFusionSystem.conjugation_closed F (valP s)).

Lemma transporter_arrow_identity (P : {group S}) :
    transporter_arrow (transporter_identity P) = DPFusionSystem.arrow_identity F P.
Proof.
apply val_inj; apply DPFusion.map_ext => x Px.
by rewrite DPFusion.conjugation_in // DPFusion.identity_in // conjg1.
Qed.

Lemma transporter_arrow_compose (P Q R : {group S})
    (s : transporter_hom P Q) (t : transporter_hom Q R) :
    transporter_arrow (transporter_compose s t) =
    DPFusionSystem.arrow_compose (transporter_arrow s) (transporter_arrow t).
Proof.
apply val_inj; apply DPFusion.map_ext => x Px.
rewrite DPFusion.conjugation_in // DPFusion.compose_in //.
rewrite DPFusion.conjugation_in ?DPFusion.map_into // DPFusion.conjugation_in //.
exact: conjgM.
Qed.

Definition transporter_projection : functor transporter_category (DPFusionSystem.fusion_category F).
Proof.
refine (@Build_functor transporter_category (DPFusionSystem.fusion_category F)
  (fun P => P) (fun P Q s => transporter_arrow s) _ _).
- exact: transporter_arrow_identity.
- exact: transporter_arrow_compose.
Defined.

Definition centric_transporter_category : category :=
  reindexed_category transporter_category (fun P : DPFusionOrbit.centric_object F => val P).

Definition centric_fusion_category : category :=
  reindexed_category (DPFusionSystem.fusion_category F)
    (fun P : DPFusionOrbit.centric_object F => val P).

Definition centric_transporter_projection : functor centric_transporter_category centric_fusion_category.
Proof.
refine (@Build_functor centric_transporter_category centric_fusion_category
  (fun P => P) (fun P Q s => transporter_arrow s) _ _).
- move=> P; exact: transporter_arrow_identity.
- move=> P Q R s t; exact: transporter_arrow_compose.
Defined.

Definition centric_fusion_inclusion : functor centric_fusion_category (DPFusionSystem.fusion_category F).
Proof.
refine (@Build_functor centric_fusion_category (DPFusionSystem.fusion_category F)
  (fun P => val P) (fun P Q f => f) _ _); reflexivity.
Defined.

End Transporters.
End DPLinkingTransporter.

Check DPLinkingTransporter.centric_transporter_projection.
Print Assumptions DPLinkingTransporter.centric_transporter_projection.
