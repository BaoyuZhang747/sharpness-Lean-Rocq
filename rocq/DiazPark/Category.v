(** Ordinary small categories, using the manuscript's left-to-right
    composition convention. This file introduces no additional axioms. *)

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Record category := {
  object : Type;
  hom : object -> object -> Type;
  identity : forall x, hom x x;
  compose : forall {x y z}, hom x y -> hom y z -> hom x z;
  compose_id_left : forall x y (f : hom x y), compose (identity x) f = f;
  compose_id_right : forall x y (f : hom x y), compose f (identity y) = f;
  compose_assoc : forall w x y z (f : hom w x) (g : hom x y) (h : hom y z),
    compose (compose f g) h = compose f (compose g h)
}.

Coercion object : category >-> Sortclass.
Arguments hom _ _ _ : clear implicits.
Arguments identity {_} _.
Arguments compose {_ _ _ _} _ _.
Arguments compose_id_left {_ _ _} _.
Arguments compose_id_right {_ _ _} _.
Arguments compose_assoc {_ _ _ _ _} _ _ _.

Definition opposite (C : category) : category.
Proof.
  refine {| object := C;
            hom := fun x y => hom C y x;
            identity := @identity C;
            compose := fun x y z f g => compose g f |}.
  - intros x y f. apply compose_id_right.
  - intros x y f. apply compose_id_left.
  - intros w x y z f g h. symmetry. apply compose_assoc.
Defined.

Record functor (C D : category) := {
  fobj : C -> D;
  fmap : forall {x y}, hom C x y -> hom D (fobj x) (fobj y);
  fmap_id : forall x, fmap (identity x) = identity (fobj x);
  fmap_compose : forall x y z (f : hom C x y) (g : hom C y z),
    fmap (compose f g) = compose (fmap f) (fmap g)
}.

Arguments fobj {_ _} _ _.
Arguments fmap {_ _} _ {_ _} _.
Arguments fmap_id {_ _} _ _.
Arguments fmap_compose {_ _} _ {_ _ _} _ _.

Definition functor_id (C : category) : functor C C.
Proof.
  refine {| fobj := fun x => x; fmap := fun x y f => f |}; reflexivity.
Defined.

Definition functor_comp {C D E : category}
    (F : functor C D) (G : functor D E) : functor C E.
Proof.
  refine {| fobj := fun x => fobj G (fobj F x);
            fmap := fun x y f => fmap G (fmap F f) |}.
  - intro x. rewrite fmap_id. apply fmap_id.
  - intros x y z f g. rewrite fmap_compose. apply fmap_compose.
Defined.

Definition functor_op {C D : category} (F : functor C D) :
    functor (opposite C) (opposite D).
Proof.
  refine (@Build_functor (opposite C) (opposite D) (fobj F)
    (fun x y f => @fmap C D F y x f) _ _).
  - intro x. exact (fmap_id F x).
  - intros x y z f g. exact (fmap_compose F g f).
Defined.

Record nat_trans {C D : category} (F G : functor C D) := {
  component : forall x, hom D (fobj F x) (fobj G x);
  naturality : forall x y (f : hom C x y),
    compose (fmap F f) (component y) = compose (component x) (fmap G f)
}.

Arguments component {_ _ _ _} _ _.
Arguments naturality {_ _ _ _} _ {_ _} _.

Definition nat_id {C D : category} (F : functor C D) : nat_trans F F.
Proof.
  refine {| component := fun x => identity (fobj F x) |}.
  intros x y f. rewrite compose_id_left, compose_id_right. reflexivity.
Defined.

Definition nat_comp {C D : category} {F G H : functor C D}
    (a : nat_trans F G) (b : nat_trans G H) : nat_trans F H.
Proof.
  refine {| component := fun x => compose (component a x) (component b x) |}.
  intros x y f.
  rewrite <- compose_assoc, (naturality a f), compose_assoc,
    (naturality b f), <- compose_assoc.
  reflexivity.
Defined.

Definition nat_whisker_left {B C D : category} (E : functor B C)
    {F G : functor C D} (a : nat_trans F G) :
    nat_trans (functor_comp E F) (functor_comp E G).
Proof.
  refine (@Build_nat_trans B D (functor_comp E F) (functor_comp E G)
    (fun x => component a (fobj E x)) _).
  intros x y f. exact (naturality a (fmap E f)).
Defined.

Definition nat_whisker_right {C D E : category}
    {F G : functor C D} (a : nat_trans F G) (H : functor D E) :
    nat_trans (functor_comp F H) (functor_comp G H).
Proof.
  refine (@Build_nat_trans C E (functor_comp F H) (functor_comp G H)
    (fun x => fmap H (component a x)) _).
  intros x y f. simpl.
  rewrite <- fmap_compose, <- fmap_compose, (naturality a f).
  reflexivity.
Defined.

Record isomorphism {C : category} (x y : C) := {
  iso_hom : hom C x y;
  iso_inv : hom C y x;
  iso_hom_inv : compose iso_hom iso_inv = identity x;
  iso_inv_hom : compose iso_inv iso_hom = identity y
}.

Arguments iso_hom {_ _ _} _.
Arguments iso_inv {_ _ _} _.
Arguments iso_hom_inv {_ _ _} _.
Arguments iso_inv_hom {_ _ _} _.

Definition iso_refl {C : category} (x : C) : isomorphism x x.
Proof.
  refine {| iso_hom := identity x; iso_inv := identity x |};
    apply compose_id_left.
Defined.

Definition iso_symm {C : category} {x y : C}
    (e : isomorphism x y) : isomorphism y x.
Proof.
  refine {| iso_hom := iso_inv e; iso_inv := iso_hom e |}.
  - apply iso_inv_hom.
  - apply iso_hom_inv.
Defined.

Definition functor_iso {C D : category} (F : functor C D)
    {x y : C} (e : isomorphism x y) : isomorphism (fobj F x) (fobj F y).
Proof.
  refine {| iso_hom := fmap F (iso_hom e); iso_inv := fmap F (iso_inv e) |}.
  - rewrite <- fmap_compose, iso_hom_inv. apply fmap_id.
  - rewrite <- fmap_compose, iso_inv_hom. apply fmap_id.
Defined.
