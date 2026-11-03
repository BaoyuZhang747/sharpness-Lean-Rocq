(** BLO's enlarged linking categories and their literal precomposition maps.
    Objects retain the actual fusion embedding into Z(P), and arrows retain
    the actual linking morphism. No centraliser comparison is assumed. *)
From mathcomp Require Import all_boot all_fingroup center boolp.
From DiazPark Require Import Category CategoryReindex CategoryIsomorphism
  FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion.
Local Open Scope group_scope.

Module DPBLODiagram.
Section Objects.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma arrow_associativity A B C D
    (f : DPFusionSystem.arrow F A B) (g : DPFusionSystem.arrow F B C)
    (h : DPFusionSystem.arrow F C D) :
    DPFusionSystem.arrow_compose (DPFusionSystem.arrow_compose f g) h =
    DPFusionSystem.arrow_compose f (DPFusionSystem.arrow_compose g h).
Proof. exact (@Category.compose_assoc (DPFusionSystem.fusion_category F) A B C D f g h). Qed.

Record enlarged_object (E : {group S}) := Point {
  underlying : DPFusionOrbit.centric_object F;
  alpha : DPFusionSystem.arrow F E 'Z(val underlying)%G
}.

Definition alpha_to_carrier E (X : enlarged_object E) :
    DPFusionSystem.arrow F E (val (underlying X)) :=
  DPFusionSystem.arrow_compose (alpha X)
    (Sub (DPFusion.inclusion (center_sub (val (underlying X))))
      (DPFusionSystem.inclusion_allowed F (center_sub (val (underlying X))))).

Lemma alpha_to_carrierE E (X : enlarged_object E) x (hx : x \in E) :
    val (alpha_to_carrier X) x = val (alpha X) x.
Proof.
rewrite /alpha_to_carrier /= DPFusion.compose_in // DPFusion.inclusion_in //.
exact: DPFusion.map_into hx.
Qed.

Variable L : DPCentricLinking.system F.
Variable E : {group S}.

Record enlarged_hom (X Y : enlarged_object E) := Arrow {
  underlying_hom : DPCentricLinking.linking_hom L (underlying X) (underlying Y);
  commutes : DPFusionSystem.arrow_compose (alpha_to_carrier X)
    (DPCentricLinking.linking_projection L underlying_hom) = alpha_to_carrier Y
}.

Lemma enlarged_hom_ext X Y (f g : enlarged_hom X Y) :
    underlying_hom f = underlying_hom g -> f = g.
Proof.
case: f=> f hf; case: g=> g hg /= e; subst g.
f_equal; apply Prop_irrelevance.
Qed.

Lemma commutesE X Y (f : enlarged_hom X Y) x (hx : x \in E) :
    val (DPCentricLinking.linking_projection L (underlying_hom f))
      (val (alpha X) x) = val (alpha Y) x.
Proof.
have h := congr1 (fun a : DPFusionSystem.arrow F E (val (underlying Y)) => val a x) (commutes f).
rewrite DPFusion.compose_in // !alpha_to_carrierE // in h.
Qed.

Definition enlarged_identity (X : enlarged_object E) : enlarged_hom X X.
Proof.
refine (@Arrow X X (DPCentricLinking.linking_identity L (underlying X)) _).
rewrite DPCentricLinking.projection_identity.
exact (@compose_id_right (DPFusionSystem.fusion_category F) E
  (val (underlying X)) (alpha_to_carrier X)).
Defined.

Definition enlarged_compose X Y Z (f : enlarged_hom X Y) (g : enlarged_hom Y Z) :
    enlarged_hom X Z.
Proof.
refine (@Arrow X Z (DPCentricLinking.linking_compose L (underlying_hom f) (underlying_hom g)) _).
rewrite DPCentricLinking.projection_compose.
by rewrite -arrow_associativity (commutes f) (commutes g).
Defined.

Definition enlarged_category : category.
Proof.
refine (@Build_category (enlarged_object E) enlarged_hom enlarged_identity
  (fun X Y Z f g => enlarged_compose f g) _ _ _).
- move=> X Y f; apply enlarged_hom_ext; exact: DPCentricLinking.linking_id_left.
- move=> X Y f; apply enlarged_hom_ext; exact: DPCentricLinking.linking_id_right.
- move=> X Y Z T f g h; apply enlarged_hom_ext; exact: DPCentricLinking.linking_assoc.
Defined.

Definition forgetful : functor enlarged_category (DPCentricLinking.linking_category L).
Proof.
refine (@Build_functor enlarged_category (DPCentricLinking.linking_category L)
  (fun X => underlying X) (fun X Y f => underlying_hom f) _ _);
  reflexivity.
Defined.

Lemma forgetful_object (X : enlarged_category) : fobj forgetful X = underlying X.
Proof. reflexivity. Qed.
Lemma forgetful_map X Y (f : hom enlarged_category X Y) :
    fmap forgetful f = underlying_hom f.
Proof. reflexivity. Qed.

Lemma enlarged_transport_map (X Y X' Y' : enlarged_category)
    (hX : X = X') (hY : Y = Y') (f : hom enlarged_category X Y) :
    underlying_hom (hom_transport hX hY f) =
    @hom_transport (DPCentricLinking.linking_category L) _ _ _ _
      (f_equal (@underlying E) hX) (f_equal (@underlying E) hY) (underlying_hom f).
Proof. destruct hX, hY; reflexivity. Qed.
End Objects.

Arguments enlarged_object {S} F E.
Arguments underlying {S F E} _.
Arguments alpha {S F E} _.
Arguments alpha_to_carrier {S F E} _.
Arguments enlarged_hom {S F} L {E} X Y.
Arguments underlying_hom {S F L E X Y} _.
Arguments enlarged_category {S F} L E.
Arguments forgetful {S F} L E.

Section Precomposition.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variables E E' : {group S}.
Variable u : DPFusionSystem.arrow F E E'.

Definition precompose_object (X : enlarged_object F E') : enlarged_object F E :=
  @Point S F E (underlying X) (DPFusionSystem.arrow_compose u (alpha X)).

Lemma precompose_alpha (X : enlarged_object F E') :
    alpha_to_carrier (precompose_object X) =
    DPFusionSystem.arrow_compose u (alpha_to_carrier X).
Proof.
exact (@Category.compose_assoc (DPFusionSystem.fusion_category F) E E'
  'Z(val (underlying X))%G (val (underlying X)) u (alpha X)
  (Sub (DPFusion.inclusion (center_sub (val (underlying X))))
    (DPFusionSystem.inclusion_allowed F (center_sub (val (underlying X)))))).
Qed.

Definition precompose_hom X Y (f : enlarged_hom L X Y) :
    enlarged_hom L (precompose_object X) (precompose_object Y).
Proof.
refine (@Arrow S F L E (precompose_object X) (precompose_object Y) (underlying_hom f) _).
rewrite !precompose_alpha.
by rewrite arrow_associativity (commutes f).
Defined.

Definition precompose : functor (enlarged_category L E') (enlarged_category L E).
Proof.
refine (@Build_functor (enlarged_category L E') (enlarged_category L E)
  precompose_object (fun X Y f => precompose_hom f) _ _).
- move=> X; apply enlarged_hom_ext; reflexivity.
- move=> X Y Z f g; apply enlarged_hom_ext; reflexivity.
Defined.

Lemma precompose_underlying X : underlying (fobj precompose X) = underlying X.
Proof. reflexivity. Qed.
Lemma precompose_map X Y (f : hom (enlarged_category L E') X Y) :
    underlying_hom (fmap precompose f) = underlying_hom f.
Proof. reflexivity. Qed.

Lemma forgetful_precompose :
    functor_comp precompose (forgetful L E) = forgetful L E'.
Proof.
apply (@functor_ext_pointwise (enlarged_category L E') (DPCentricLinking.linking_category L)
  (functor_comp precompose (forgetful L E)) (forgetful L E')
  (fun X => Logic.eq_refl (underlying X))).
move=> X Y f; reflexivity.
Qed.
End Precomposition.

Arguments precompose_object {S F E E'} u X.
Arguments precompose {S F} L {E E'} u.

Section PrecompositionLaws.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.

Lemma precompose_object_identity E (X : enlarged_object F E) :
    precompose_object (DPFusionSystem.arrow_identity F E) X = X.
Proof.
case: X=> P a; congr (@Point _ _ _ P _).
exact (@compose_id_left (DPFusionSystem.fusion_category F) E 'Z(val P)%G a).
Qed.

Lemma precompose_identity E :
    precompose L (DPFusionSystem.arrow_identity F E) = functor_id (enlarged_category L E).
Proof.
apply (@functor_ext_pointwise (enlarged_category L E) (enlarged_category L E)
  (precompose L (DPFusionSystem.arrow_identity F E)) (functor_id (enlarged_category L E))
  (@precompose_object_identity E)).
move=> X Y f; apply enlarged_hom_ext; rewrite enlarged_transport_map.
exact (@hom_transport_loop (DPCentricLinking.linking_category L)
  (underlying X) (underlying Y) _ _ (underlying_hom f)).
Qed.

Lemma precompose_object_composition E E' E''
    (u : DPFusionSystem.arrow F E E') (v : DPFusionSystem.arrow F E' E'')
    (X : enlarged_object F E'') :
    precompose_object (DPFusionSystem.arrow_compose u v) X =
    precompose_object u (precompose_object v X).
Proof.
case: X=> P a; congr (@Point _ _ _ P _).
exact (@Category.compose_assoc (DPFusionSystem.fusion_category F) E E' E'' 'Z(val P)%G u v a).
Qed.

Lemma precompose_composition E E' E''
    (u : DPFusionSystem.arrow F E E') (v : DPFusionSystem.arrow F E' E'') :
    precompose L (DPFusionSystem.arrow_compose u v) =
    functor_comp (precompose L v) (precompose L u).
Proof.
apply (@functor_ext_pointwise (enlarged_category L E'') (enlarged_category L E)
  (precompose L (DPFusionSystem.arrow_compose u v))
  (functor_comp (precompose L v) (precompose L u))
  (@precompose_object_composition E E' E'' u v)).
move=> X Y f; apply enlarged_hom_ext; rewrite enlarged_transport_map.
exact (@hom_transport_loop (DPCentricLinking.linking_category L)
  (underlying X) (underlying Y) _ _ (underlying_hom f)).
Qed.
End PrecompositionLaws.
End DPBLODiagram.
