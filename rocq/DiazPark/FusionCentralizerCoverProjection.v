From mathcomp Require Import all_ssreflect all_fingroup center abelian generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionCentralizerCover FusionCentralizerCompression.
Import DPFusion DPFusionOrbit DPFusionCentralizerCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverProjection.
Section Projection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Local Notation Ob := (cover_object F p).

Definition elementary_pred (E : {group S}) :=
  [&& E :!=: 1, p.-abelem E & DPFusionSystem.fully_centralized F E].
Definition elementary_object := {E : {group S} | elementary_pred E}.
Definition elementary_category : category.
Proof.
refine (@Build_category elementary_object
  (fun E D => DPFusionSystem.arrow F (val E) (val D))
  (fun E => DPFusionSystem.arrow_identity F (val E))
  (fun E D A f g => @DPFusionSystem.arrow_compose S F (val E) (val D) (val A) f g) _ _ _).
- move=> E D f; exact: (@Category.compose_id_left (DPFusionSystem.fusion_category F) (val E) (val D) f).
- move=> E D f; exact: (@Category.compose_id_right (DPFusionSystem.fusion_category F) (val E) (val D) f).
- move=> E D A B f g h; exact: (@Category.compose_assoc (DPFusionSystem.fusion_category F) (val E) (val D) (val A) (val B) f g h).
Defined.

Variables X Y : Ob.
Variable raw : DPFusionSystem.arrow F (carrier X) (carrier Y).
Hypothesis hraw : raw_condition raw.

Definition restricted := DPFusion.restrict (val raw) (elementary_sub X).
Lemma target_sub_restricted_image : elementary Y \subset DPFusion.image restricted.
Proof.
rewrite /restricted DPFusionCentralizerCompression.restricted_image.
exact hraw.
Qed.
Definition raw_delta : DPFusion.map (elementary Y) (elementary X) :=
  DPFusion.restrict (DPFusion.inverse restricted) target_sub_restricted_image.

Lemma raw_delta_allowed : DPFusionSystem.allowed F raw_delta.
Proof.
apply: DPFusionSystem.restriction_allowed.
apply: DPFusionSystem.inverse_closed.
exact: DPFusionSystem.restriction_allowed (valP raw).
Qed.

Lemma raw_deltaE : {in elementary Y, forall x, val raw (raw_delta x) = x}.
Proof.
move=> x Ex.
have Ix := subsetP target_sub_restricted_image x Ex.
rewrite /raw_delta DPFusion.restrict_in //.
have h := DPFusion.inverse_cancel_right Ix.
change (restricted (DPFusion.inverse restricted x) = x) in h.
by rewrite /restricted DPFusion.restrict_in ?DPFusion.map_into // in h.
Qed.

Lemma raw_delta_unique (g : DPFusion.map (elementary Y) (elementary X)) :
  {in elementary Y, forall x, val raw (g x) = x} -> g = raw_delta.
Proof.
move=> hg; apply: DPFusion.map_ext=> x Ex.
apply: (DPFusion.map_injective (f := val raw)
  (subsetP (elementary_sub X) _ (DPFusion.map_into g Ex))
  (subsetP (elementary_sub X) _ (DPFusion.map_into raw_delta Ex))).
by rewrite hg // raw_deltaE.
Qed.
End Projection.

Section OrbitProjection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Local Notation Ob := (cover_object F p).

Lemma raw_delta_inner (X Y : Ob)
    (f g : DPFusionSystem.arrow F (carrier X) (carrier Y))
    (hf : raw_condition f) (hg : raw_condition g) :
  target_inner f g -> raw_delta hf = raw_delta hg.
Proof.
move=> /exists_inP[t Yt /forall_inP ht].
apply: raw_delta_unique=> x Ex.
have h := eqP (ht (raw_delta hf x)
  (subsetP (elementary_sub X) _ (DPFusion.map_into (raw_delta hf) Ex))).
change (val g (raw_delta hf x) = (val f (raw_delta hf x))^t) in h.
rewrite h raw_deltaE //.
apply/conjg_fixP/commgP.
exact: (centP (setIP (subsetP (elementary_center Y) x Ex)).2 t Yt).
Qed.

Definition delta (X Y : Ob) (f : cover_hom X Y) :
    DPFusion.map (elementary Y) (elementary X) := raw_delta (valP f).
Lemma delta_allowed (X Y : Ob) (f : cover_hom X Y) : DPFusionSystem.allowed F (delta f).
Proof. exact: raw_delta_allowed. Qed.

Definition cover_class (X Y : Ob)
    (f : DPFusionSystem.arrow F (carrier X) (carrier Y)) (hf : raw_condition f) : cover_hom X Y :=
  Sub (orbit_class f) (eq_ind_r is_true hf (condition_class f)).

Lemma delta_class (X Y : Ob)
    (f : DPFusionSystem.arrow F (carrier X) (carrier Y)) (hf : raw_condition f) :
  delta (cover_class hf) = raw_delta hf.
Proof. exact: raw_delta_inner (representative_related f). Qed.

Lemma delta_identity (X : Ob) : delta (cover_identity X) = DPFusion.identity (elementary X).
Proof.
apply/esym/raw_delta_unique=> x Ex.
have Xx := subsetP (elementary_sub X) x Ex.
rewrite DPFusion.identity_in //.
have rel := representative_related (DPFusionSystem.arrow_identity F (carrier X)).
move/exists_inP: rel=> [t Xt /forall_inP ht].
have e := eqP (ht x (subsetP (elementary_sub X) x Ex)).
change (DPFusion.identity (carrier X) x = (val (repr (orbit_identity F (carrier X))) x)^t) in e.
rewrite DPFusion.identity_in // in e.
have h := congr1 (fun z : S => z^t^-1) e.
rewrite conjgK in h.
rewrite -h; apply/conjg_fixP/commgP.
have XtV : t^-1 \in carrier X by rewrite groupV.
exact: (centP (setIP (subsetP (elementary_center X) x Ex)).2 t^-1 XtV).
Qed.

Lemma delta_compose (X Y Z : Ob) (f : cover_hom X Y) (g : cover_hom Y Z) :
  delta (cover_compose f g) = DPFusion.compose (delta g) (delta f).
Proof.
have ec : cover_compose f g =
    cover_class (raw_condition_compose (valP f) (valP g)).
  apply: val_inj; by [].
rewrite ec delta_class.
apply/esym/raw_delta_unique=> x Ex.
rewrite DPFusion.compose_in //.
have Ey := DPFusion.map_into (delta g) Ex.
have Xz := subsetP (elementary_sub X) _ (DPFusion.map_into (delta f) Ey).
change (DPFusion.compose (val (repr (val f))) (val (repr (val g)))
  (delta f (delta g x)) = x).
rewrite DPFusion.compose_in //.
rewrite (raw_deltaE (valP f) Ey) (raw_deltaE (valP g) Ex).
by [].
Qed.

Definition projection_object (X : centralized_object F p) : elementary_object F p.
Proof.
exists (elementary (val X)); apply/and3P; split.
- exact: elementary_nontrivial.
- exact: elementary_abelem.
- exact: valP X.
Defined.

Definition projection_arrow (X Y : centralized_object F p)
    (f : cover_hom (val X) (val Y)) :
    DPFusionSystem.arrow F (val (projection_object Y)) (val (projection_object X)) :=
  Sub (delta f) (delta_allowed f).

Definition projection : functor (centralized_category F p) (opposite (elementary_category F p)).
Proof.
refine (@Build_functor (centralized_category F p) (opposite (elementary_category F p))
  projection_object (fun X Y f => projection_arrow f) _ _).
- move=> X; apply: val_inj; exact: delta_identity.
- move=> X Y Z f g; apply: val_inj; exact: delta_compose.
Defined.

End OrbitProjection.
End DPFusionCentralizerCoverProjection.






