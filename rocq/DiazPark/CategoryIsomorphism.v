From mathcomp Require Import boolp.
From DiazPark Require Import Category.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Literal inverse functors, not merely an equivalence up to natural
    isomorphism. The equality lemma exposes the standard extensionality
    principles already used by the functor-category infrastructure. *)
Record category_isomorphism (C D : category) := {
  category_iso_forward : functor C D;
  category_iso_backward : functor D C;
  category_iso_forward_backward :
    functor_comp category_iso_forward category_iso_backward = functor_id C;
  category_iso_backward_forward :
    functor_comp category_iso_backward category_iso_forward = functor_id D
}.

Definition functor_hom_type {C D : category} (fo : C -> D) :=
  forall x y, hom C x y -> hom D (fo x) (fo y).

Lemma functor_extensionality {C D : category} (F G : functor C D)
    (ho : fobj F = fobj G) :
  eq_rect (fobj F) (@functor_hom_type C D) (@fmap C D F) (fobj G) ho =
    @fmap C D G -> F = G.
Proof.
destruct F as [fo fm fi fc], G as [go gm gi gc]; simpl in *.
destruct ho; simpl; intro hm; destruct hm.
f_equal; apply Prop_irrelevance.
Qed.

Definition category_iso_symm {C D : category} (e : category_isomorphism C D) :
    category_isomorphism D C :=
  {| category_iso_forward := category_iso_backward e;
     category_iso_backward := category_iso_forward e;
     category_iso_forward_backward := category_iso_backward_forward e;
     category_iso_backward_forward := category_iso_forward_backward e |}.

Definition category_iso_refl (C : category) : category_isomorphism C C.
Proof.
refine {| category_iso_forward := functor_id C;
          category_iso_backward := functor_id C |};
  apply (@functor_extensionality C C
    (functor_comp (functor_id C) (functor_id C)) (functor_id C) eq_refl); reflexivity.
Defined.

Lemma functor_comp_assoc {A B C D : category}
    (F : functor A B) (G : functor B C) (H : functor C D) :
  functor_comp (functor_comp F G) H = functor_comp F (functor_comp G H).
Proof.
  apply (@functor_extensionality A D (functor_comp (functor_comp F G) H)
    (functor_comp F (functor_comp G H)) eq_refl); reflexivity.
Qed.

Lemma functor_comp_id_left {C D : category} (F : functor C D) :
  functor_comp (functor_id C) F = F.
Proof.
  apply (@functor_extensionality C D (functor_comp (functor_id C) F) F eq_refl);
    reflexivity.
Qed.

Lemma functor_comp_id_right {C D : category} (F : functor C D) :
  functor_comp F (functor_id D) = F.
Proof.
  apply (@functor_extensionality C D (functor_comp F (functor_id D)) F eq_refl);
    reflexivity.
Qed.

Definition category_iso_trans {A B C : category}
    (e : category_isomorphism A B) (f : category_isomorphism B C) :
    category_isomorphism A C.
Proof.
  refine {| category_iso_forward := functor_comp (category_iso_forward e) (category_iso_forward f);
            category_iso_backward := functor_comp (category_iso_backward f) (category_iso_backward e) |}.
  - rewrite functor_comp_assoc, <- (functor_comp_assoc (category_iso_forward f)),
      category_iso_forward_backward, functor_comp_id_left.
    exact (category_iso_forward_backward e).
  - rewrite functor_comp_assoc, <- (functor_comp_assoc (category_iso_backward e)),
      category_iso_backward_forward, functor_comp_id_left.
    exact (category_iso_backward_forward f).
Defined.

Definition category_iso_of_eq {C D : category} (h : C = D) :
    category_isomorphism C D :=
  match h with eq_refl => category_iso_refl C end.
