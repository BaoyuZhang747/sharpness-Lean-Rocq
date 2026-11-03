From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems.
Import DPFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionOrbit.
Section Orbit.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Definition arrow_value (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :=
  DPFusion.map_fun (val f).

(** Equality modulo actual inner conjugations in the named target group. *)
Definition target_inner (P Q : {group S}) (f g : DPFusionSystem.arrow F P Q) :=
  [exists r in Q, [forall x in P, arrow_value g x == (arrow_value f x) ^ r]].

Lemma target_inner_refl (P Q : {group S}) : reflexive (@target_inner P Q).
Proof.
move=> f; apply/exists_inP; exists (1 : S); first exact: group1.
by apply/forall_inP=> x Px; rewrite conjg1.
Qed.

Lemma target_inner_reverse (P Q : {group S}) (f g : DPFusionSystem.arrow F P Q) :
  target_inner f g -> target_inner g f.
Proof.
move=> /exists_inP[r Qr /forall_inP hr].
apply/exists_inP; exists r^-1; first by rewrite groupV.
apply/forall_inP=> x Px; by rewrite (eqP (hr x Px)) conjgK.
Qed.

Lemma target_inner_sym (P Q : {group S}) : symmetric (@target_inner P Q).
Proof. move=> f g; apply/idP/idP; exact: target_inner_reverse. Qed.

Lemma target_inner_trans (P Q : {group S}) : transitive (@target_inner P Q).
Proof.
move=> f g h /exists_inP[r Qr /forall_inP hr]
  /exists_inP[t Qt /forall_inP ht].
apply/exists_inP; exists (r * t); first exact: groupM Qr Qt.
apply/forall_inP=> x Px.
by rewrite (eqP (ht x Px)) (eqP (hr x Px)) conjgM.
Qed.

Lemma target_inner_precompose (P Q R : {group S})
    (f : DPFusionSystem.arrow F P Q) (g g' : DPFusionSystem.arrow F Q R) :
  target_inner g g' ->
  target_inner (DPFusionSystem.arrow_compose f g) (DPFusionSystem.arrow_compose f g').
Proof.
move=> /exists_inP[r Rr /forall_inP hr].
apply/exists_inP; exists r => //; apply/forall_inP=> x Px.
rewrite /arrow_value /DPFusionSystem.arrow_compose /= !DPFusion.compose_in //.
exact: hr (DPFusion.map_fun (val f) x) (DPFusion.map_into (val f) Px).
Qed.

Lemma target_inner_postcompose (P Q R : {group S})
    (f f' : DPFusionSystem.arrow F P Q) (g : DPFusionSystem.arrow F Q R) :
  target_inner f f' ->
  target_inner (DPFusionSystem.arrow_compose f g) (DPFusionSystem.arrow_compose f' g).
Proof.
move=> /exists_inP[r Qr /forall_inP hr].
apply/exists_inP; exists (arrow_value g r); first exact: DPFusion.map_into Qr.
apply/forall_inP=> x Px; apply/eqP.
rewrite /arrow_value /DPFusionSystem.arrow_compose /= !DPFusion.compose_in //.
rewrite /arrow_value in hr.
rewrite (eqP (hr x Px)).
apply: (morphJ (DPFusion.map_morphism (val g)))=> //.
exact: DPFusion.map_into Px.
Qed.

Lemma target_inner_compose (P Q R : {group S})
    (f f' : DPFusionSystem.arrow F P Q) (g g' : DPFusionSystem.arrow F Q R) :
  target_inner f f' -> target_inner g g' ->
  target_inner (DPFusionSystem.arrow_compose f g) (DPFusionSystem.arrow_compose f' g').
Proof.
move=> hff hgg.
exact: (@target_inner_trans P R _ _ _
  (@target_inner_postcompose P Q R f f' g hff)
  (@target_inner_precompose P Q R f' g g' hgg)).
Qed.

Definition inner_equiv (P Q : {group S}) :=
  EquivRel (@target_inner P Q) (@target_inner_refl P Q)
    (@target_inner_sym P Q) (@target_inner_trans P Q).

Definition orbit_hom (P Q : {group S}) := {eq_quot (inner_equiv P Q)}.

#[export] HB.instance Definition _ (P Q : {group S}) :=
  [Finite of orbit_hom P Q by <:%/].

Definition orbit_class (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
  orbit_hom P Q := \pi_(orbit_hom P Q) f.

Lemma orbit_class_eq (P Q : {group S}) (f g : DPFusionSystem.arrow F P Q) :
  reflect (orbit_class f = orbit_class g) (target_inner f g).
Proof. exact: eqmodP. Qed.

Lemma representative_related (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
  target_inner (repr (orbit_class f)) f.
Proof. apply/orbit_class_eq; exact: reprK. Qed.

Definition orbit_compose (P Q R : {group S}) (f : orbit_hom P Q) (g : orbit_hom Q R) :
  orbit_hom P R := orbit_class (DPFusionSystem.arrow_compose (repr f) (repr g)).

Lemma orbit_compose_class (P Q R : {group S})
    (f : DPFusionSystem.arrow F P Q) (g : DPFusionSystem.arrow F Q R) :
  orbit_compose (orbit_class f) (orbit_class g) =
  orbit_class (DPFusionSystem.arrow_compose f g).
Proof.
apply/orbit_class_eq; apply: target_inner_compose; exact: representative_related.
Qed.

Definition orbit_identity (P : {group S}) : orbit_hom P P :=
  orbit_class (DPFusionSystem.arrow_identity F P).

Definition orbit_category : category.
Proof.
refine (@Build_category {group S} orbit_hom orbit_identity
  (fun P Q R f g => @orbit_compose P Q R f g) _ _ _).
- move=> P Q; apply: quotW=> f.
  rewrite /orbit_identity orbit_compose_class.
  apply: congr1; apply: val_inj; exact: DPFusion.identity_compose.
- move=> P Q; apply: quotW=> f.
  rewrite /orbit_identity orbit_compose_class.
  apply: congr1; apply: val_inj; exact: DPFusion.compose_identity.
- move=> P Q R T; apply: quotW=> f; apply: quotW=> g; apply: quotW=> h.
  rewrite (orbit_compose_class f g) (orbit_compose_class g h) !orbit_compose_class.
  apply: congr1; apply: val_inj; exact: DPFusion.compose_assoc.
Defined.

Definition quotient_functor : functor (DPFusionSystem.fusion_category F) orbit_category.
Proof.
refine (@Build_functor (DPFusionSystem.fusion_category F) orbit_category
  (fun P => P) (fun P Q f => orbit_class f) _ _).
- by move=> P.
- move=> P Q R f g; exact: esym (orbit_compose_class f g).
Defined.

(** The category is genuinely finite: these are inherited finite structures. *)
Definition orbit_objects_enum : seq {group S} := enum {group S}.
Definition orbit_hom_enum (P Q : {group S}) : seq (orbit_hom P Q) :=
  enum [set: orbit_hom P Q].

Lemma orbit_hom_enum_complete (P Q : {group S}) (f : orbit_hom P Q) :
  f \in orbit_hom_enum P Q.
Proof. by rewrite /orbit_hom_enum mem_enum inE. Qed.

Definition centric_object := {P : {group S} | DPFusionSystem.centric F P}.

Definition centric_orbit_category : category.
Proof.
refine (@Build_category centric_object
  (fun P Q => orbit_hom (val P) (val Q))
  (fun P => orbit_identity (val P))
  (fun P Q R f g => @orbit_compose (val P) (val Q) (val R) f g) _ _ _).
- move=> P Q f; exact: (@Category.compose_id_left orbit_category (val P) (val Q) f).
- move=> P Q f; exact: (@Category.compose_id_right orbit_category (val P) (val Q) f).
- move=> P Q R T f g h.
  exact: (@Category.compose_assoc orbit_category (val P) (val Q) (val R) (val T) f g h).
Defined.

Definition centric_inclusion : functor centric_orbit_category orbit_category.
Proof.
refine (@Build_functor centric_orbit_category orbit_category
  (fun P => val P) (fun P Q f => f) _ _); by [].
Defined.

Definition centric_objects_enum : seq centric_object := enum [set: centric_object].

Lemma orbit_class_eq_iff (P Q : {group S}) (f g : DPFusionSystem.arrow F P Q) :
  orbit_class f = orbit_class g <->
  exists r : S, r \in Q /\ {in P, forall x, arrow_value g x = (arrow_value f x) ^ r}.
Proof.
split=> [/orbit_class_eq/exists_inP[r Qr /forall_inP hr] | [r [Qr hr]]].
- exists r; split=> // x Px; exact: eqP (hr x Px).
- apply/orbit_class_eq/exists_inP; exists r=> //; apply/forall_inP=> x Px.
  apply/eqP; exact: hr x Px.
Qed.

End Orbit.
End DPFusionOrbit.
