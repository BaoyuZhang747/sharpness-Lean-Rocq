From mathcomp Require Import all_ssreflect all_fingroup center abelian generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
Import DPFusion DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCover.
Section Cover.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.

Definition object_pred (PE : centric_object F * {group S}) :=
  [&& PE.2 :!=: 1, p.-abelem PE.2 & PE.2 \subset 'Z(val PE.1)].
Definition cover_object := {PE : centric_object F * {group S} | object_pred PE}.
Definition underlying (X : cover_object) : centric_object F := (val X).1.
Definition elementary (X : cover_object) : {group S} := (val X).2.
Definition carrier (X : cover_object) : {group S} := val (underlying X).

Lemma elementary_nontrivial X : elementary X :!=: 1.
Proof. by have /and3P[] := valP X. Qed.
Lemma elementary_abelem X : p.-abelem (elementary X).
Proof. by have /and3P[] := valP X. Qed.
Lemma elementary_center X : elementary X \subset 'Z(carrier X).
Proof. by have /and3P[] := valP X. Qed.
Lemma elementary_sub X : elementary X \subset carrier X.
Proof. exact: subset_trans (elementary_center X) (center_sub (carrier X)). Qed.
Lemma carrier_centric X : DPFusionSystem.centric F (carrier X).
Proof. exact: valP (underlying X). Qed.

Definition raw_condition (X Y : cover_object)
    (f : DPFusionSystem.arrow F (carrier X) (carrier Y)) :=
  elementary Y \subset DPFusion.map_morphism (val f) @* elementary X.

Lemma raw_condition_inner_forward (X Y : cover_object)
    (f g : DPFusionSystem.arrow F (carrier X) (carrier Y)) :
  target_inner f g -> raw_condition f -> raw_condition g.
Proof.
move=> /exists_inP[t Yt /forall_inP ht] hf.
apply/subsetP=> z Ez.
have /morphimP[x Xx Ex ez] := subsetP hf z Ez.
change (z = val f x) in ez.
apply/morphimP; exists x=> //.
change (z = val g x).
have e := eqP (ht x Xx).
change (val g x = (val f x)^t) in e.
rewrite e -ez; apply/esym/conjg_fixP/commgP.
have zC := (setIP (subsetP (elementary_center Y) z Ez)).2.
exact: (centP zC t Yt).
Qed.

Lemma raw_condition_inner (X Y : cover_object)
    (f g : DPFusionSystem.arrow F (carrier X) (carrier Y)) :
  target_inner f g -> raw_condition f = raw_condition g.
Proof.
move=> h; apply/idP/idP.
- exact: raw_condition_inner_forward h.
- exact: raw_condition_inner_forward (target_inner_reverse h).
Qed.

Definition condition (X Y : cover_object) (f : orbit_hom F (carrier X) (carrier Y)) :=
  raw_condition (repr f).

Lemma condition_class (X Y : cover_object)
    (f : DPFusionSystem.arrow F (carrier X) (carrier Y)) :
  condition (orbit_class f) = raw_condition f.
Proof. exact: raw_condition_inner (representative_related f). Qed.

Lemma condition_identity (X : cover_object) : condition (orbit_identity F (carrier X)).
Proof.
rewrite /orbit_identity condition_class.
apply/subsetP=> x Ex; have Xx := subsetP (elementary_sub X) x Ex.
apply/morphimP; exists x=> //.
change (x = DPFusion.identity (carrier X) x).
by rewrite DPFusion.identity_in.
Qed.

Lemma raw_condition_compose (X Y Z : cover_object)
    (f : DPFusionSystem.arrow F (carrier X) (carrier Y))
    (g : DPFusionSystem.arrow F (carrier Y) (carrier Z)) :
  raw_condition f -> raw_condition g ->
  raw_condition (DPFusionSystem.arrow_compose f g).
Proof.
move=> hf hg; apply/subsetP=> z Ez.
have /morphimP[y Yy Ey ez] := subsetP hg z Ez.
have /morphimP[x Xx Ex ey] := subsetP hf y Ey.
apply/morphimP; exists x=> //.
change (z = DPFusion.compose (val f) (val g) x).
change (z = val g y) in ez; change (y = val f x) in ey.
by rewrite DPFusion.compose_in // -ey -ez.
Qed.

Lemma condition_compose (X Y Z : cover_object)
    (f : orbit_hom F (carrier X) (carrier Y))
    (g : orbit_hom F (carrier Y) (carrier Z)) :
  condition f -> condition g -> condition (orbit_compose f g).
Proof.
move=> hf hg; rewrite /orbit_compose condition_class.
exact: raw_condition_compose hf hg.
Qed.

Definition cover_hom (X Y : cover_object) :=
  {f : orbit_hom F (carrier X) (carrier Y) | condition f}.
Definition cover_identity X : cover_hom X X := Sub _ (condition_identity X).
Definition cover_compose (X Y Z : cover_object) (f : cover_hom X Y) (g : cover_hom Y Z) :
  cover_hom X Z := Sub (orbit_compose (val f) (val g)) (condition_compose (valP f) (valP g)).

Definition cover_category : category.
Proof.
refine (@Build_category cover_object cover_hom cover_identity
  (fun X Y Z f g => @cover_compose X Y Z f g) _ _ _).
- move=> X Y f; apply: val_inj.
  exact: (@Category.compose_id_left (orbit_category F) (carrier X) (carrier Y) (val f)).
- move=> X Y f; apply: val_inj.
  exact: (@Category.compose_id_right (orbit_category F) (carrier X) (carrier Y) (val f)).
- move=> W X Y Z f g h; apply: val_inj.
  exact: (@Category.compose_assoc (orbit_category F) (carrier W) (carrier X) (carrier Y) (carrier Z)
    (val f) (val g) (val h)).
Defined.

Definition forget : functor cover_category (centric_orbit_category F).
Proof.
refine (@Build_functor cover_category (centric_orbit_category F) underlying
  (fun X Y f => val f) _ _); by [].
Defined.

Lemma forget_faithful (X Y : cover_object) :
  injective (@fmap cover_category (centric_orbit_category F) forget X Y).
Proof. exact: val_inj. Qed.

Definition centralized_object := {X : cover_object | DPFusionSystem.fully_centralized F (elementary X)}.
Definition centralized_category : category.
Proof.
refine (@Build_category centralized_object
  (fun X Y => cover_hom (val X) (val Y))
  (fun X => cover_identity (val X))
  (fun X Y Z f g => @cover_compose (val X) (val Y) (val Z) f g) _ _ _).
- move=> X Y f; exact: (@Category.compose_id_left cover_category (val X) (val Y) f).
- move=> X Y f; exact: (@Category.compose_id_right cover_category (val X) (val Y) f).
- move=> W X Y Z f g h; exact: (@Category.compose_assoc cover_category (val W) (val X) (val Y) (val Z) f g h).
Defined.

Definition centralized_inclusion : functor centralized_category cover_category.
Proof.
refine (@Build_functor centralized_category cover_category val
  (fun X Y f => f) _ _); by [].
Defined.

End Cover.
End DPFusionCentralizerCover.




