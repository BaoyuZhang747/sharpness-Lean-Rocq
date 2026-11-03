(** The actual varying-target comma category and its projection square. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryReindex.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryQuillenATotalComma.
Section Total.
Variables C D : category.
Variable T : functor C D.

Record total_object := {
  source : C;
  target : D;
  arrow : hom D (fobj T source) target
}.

Record total_hom (x y : total_object) := {
  source_map : hom C (source x) (source y);
  target_map : hom D (target x) (target y);
  square : compose (fmap T source_map) (arrow y) = compose (arrow x) target_map
}.

Lemma total_hom_ext x y (f g : total_hom x y) :
  source_map f = source_map g -> target_map f = target_map g -> f = g.
Proof.
destruct f as [f h e], g as [g k d]; cbn; intros ef eh; subst g k.
f_equal; apply Prop_irrelevance.
Qed.

Definition total_identity x : total_hom x x.
Proof.
refine (@Build_total_hom x x (identity (source x)) (identity (target x)) _).
by rewrite fmap_id compose_id_left compose_id_right.
Defined.

Definition total_compose x y z (f : total_hom x y) (g : total_hom y z) : total_hom x z.
Proof.
refine (@Build_total_hom x z (compose (source_map f) (source_map g))
  (compose (target_map f) (target_map g)) _).
by rewrite fmap_compose compose_assoc (square g) -compose_assoc (square f) compose_assoc.
Defined.

Definition total_category : category.
Proof.
refine (@Build_category total_object total_hom total_identity (@total_compose) _ _ _).
- intros; apply total_hom_ext; apply compose_id_left.
- intros; apply total_hom_ext; apply compose_id_right.
- intros; apply total_hom_ext; apply compose_assoc.
Defined.

Definition source_projection : functor total_category C.
Proof. refine (@Build_functor total_category C source (fun _ _ f => source_map f) _ _); reflexivity. Defined.

Definition target_projection : functor total_category D.
Proof. refine (@Build_functor total_category D target (fun _ _ f => target_map f) _ _); reflexivity. Defined.

Definition projection_transformation : nat_trans (functor_comp source_projection T) target_projection.
Proof.
refine (@Build_nat_trans total_category D (functor_comp source_projection T) target_projection arrow _).
intros; exact: square.
Defined.

Lemma object_arrow_eq (c : C) (d : D) (h k : hom D (fobj T c) d) :
  h = k -> @Build_total_object c d h = @Build_total_object c d k.
Proof. intro e; subst k; reflexivity. Qed.

Lemma source_transport (x y x' y' : total_category) (hx : x=x') (hy : y=y')
    (f : hom total_category x y) :
  source_map (hom_transport hx hy f) = hom_transport (f_equal source hx) (f_equal source hy) (source_map f).
Proof. destruct hx,hy; reflexivity. Qed.

Lemma target_transport (x y x' y' : total_category) (hx : x=x') (hy : y=y')
    (f : hom total_category x y) :
  target_map (hom_transport hx hy f) = hom_transport (f_equal target hx) (f_equal target hy) (target_map f).
Proof. destruct hx,hy; reflexivity. Qed.
End Total.
End DPCategoryQuillenATotalComma.

