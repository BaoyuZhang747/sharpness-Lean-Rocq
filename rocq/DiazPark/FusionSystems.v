From mathcomp Require Import all_ssreflect all_fingroup.
From DiazPark Require Import Category FusionMaps.

(** Ordinary fusion systems on all actual subgroups of a finite group.
    Only conjugation, composition and image-isomorphism closure are fields.
    Saturation and every generation/cohomology theorem are separate. *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionSystem.

Section Systems.
Variable S : finGroupType.

Record system := FusionSystem {
  allowed : forall P Q : {group S}, DPFusion.map P Q -> bool;
  conjugation_closed : forall (P Q : {group S}) (s : S)
    (sPQ : P :^ s \subset Q), @allowed P Q (DPFusion.conjugation sPQ);
  composition_closed : forall (P Q R : {group S})
    (f : DPFusion.map P Q) (g : DPFusion.map Q R),
    @allowed P Q f -> @allowed Q R g -> @allowed P R (DPFusion.compose f g);
  image_closed : forall (P Q : {group S}) (f : DPFusion.map P Q),
    @allowed P Q f -> @allowed P (DPFusion.image f) (DPFusion.to_image f);
  inverse_closed : forall (P Q : {group S}) (f : DPFusion.map P Q),
    @allowed P Q f -> @allowed (DPFusion.image f) P (DPFusion.inverse f)
}.

Arguments allowed _ {P Q} _.

Variable F : system.

Lemma inclusion_allowed (P Q : {group S}) (sPQ : P \subset Q) :
  allowed F (DPFusion.inclusion sPQ).
Proof.
have sP1Q : P :^ (1 : S) \subset Q by rewrite conjsg1.
have h := conjugation_closed F sP1Q.
have eqf : DPFusion.conjugation sP1Q = DPFusion.inclusion sPQ.
  apply: DPFusion.map_ext=> x Px.
  by rewrite DPFusion.conjugation_in // DPFusion.inclusion_in // conjg1.
by rewrite eqf in h.
Qed.

Lemma identity_allowed (P : {group S}) : allowed F (DPFusion.identity P).
Proof. exact: inclusion_allowed. Qed.

Lemma corestriction_allowed (P Q R : {group S}) (f : DPFusion.map P Q)
    (sIR : DPFusion.image f \subset R) :
  allowed F f -> allowed F (DPFusion.corestrict sIR).
Proof.
move=> hf.
have h := composition_closed (image_closed hf) (inclusion_allowed sIR).
have eqf : DPFusion.compose (DPFusion.to_image f) (DPFusion.inclusion sIR) =
    DPFusion.corestrict sIR.
  apply: DPFusion.map_ext=> x Px.
  rewrite DPFusion.compose_in // DPFusion.inclusion_in ?DPFusion.map_into //.
by rewrite eqf in h.
Qed.

Lemma restriction_allowed (P Q A : {group S}) (f : DPFusion.map P Q)
    (sAP : A \subset P) :
  allowed F f -> allowed F (DPFusion.restrict f sAP).
Proof.
move=> hf.
have h := composition_closed (inclusion_allowed sAP) hf.
have eqf : DPFusion.compose (DPFusion.inclusion sAP) f = DPFusion.restrict f sAP.
  apply: DPFusion.map_ext=> x Ax.
  by rewrite DPFusion.compose_in // DPFusion.inclusion_in // DPFusion.restrict_in.
by rewrite eqf in h.
Qed.

Definition arrow (P Q : {group S}) := {f : DPFusion.map P Q | allowed F f}.

Definition arrow_identity (P : {group S}) : arrow P P :=
  Sub (DPFusion.identity P) (identity_allowed P).

Definition arrow_compose (P Q R : {group S}) (f : arrow P Q) (g : arrow Q R) :
    arrow P R :=
  Sub (DPFusion.compose (val f) (val g)) (composition_closed (valP f) (valP g)).

Lemma arrow_ext (P Q : {group S}) (f g : arrow P Q) :
  {in P, DPFusion.map_fun (val f) =1 DPFusion.map_fun (val g)} -> f = g.
Proof. move=> h; apply: val_inj; exact: DPFusion.map_ext h. Qed.

Definition fusion_category : category.
Proof.
refine (@Build_category {group S} arrow arrow_identity
  (fun P Q R f g => @arrow_compose P Q R f g) _ _ _).
- move=> P Q f; apply: val_inj.
  exact: DPFusion.identity_compose.
- move=> P Q f; apply: val_inj.
  exact: DPFusion.compose_identity.
- move=> P Q R T f g h; apply: val_inj.
  exact: DPFusion.compose_assoc.
Defined.

(** Fusion conjugacy requires an allowed map onto exactly the named subgroup. *)
Definition conjugate (P Q : {group S}) :=
  [exists f : DPFusion.map P Q, allowed F f && (DPFusion.image f == Q)].

Definition fully_normalized (P : {group S}) :=
  [forall Q : {group S}, conjugate P Q ==> (#|'N(Q)| <= #|'N(P)|)%N].

Definition fully_centralized (P : {group S}) :=
  [forall Q : {group S}, conjugate P Q ==> (#|'C(Q)| <= #|'C(P)|)%N].

Definition centric (P : {group S}) :=
  [forall Q : {group S}, conjugate P Q ==> ('C(Q) \subset Q)].

End Systems.

End DPFusionSystem.
