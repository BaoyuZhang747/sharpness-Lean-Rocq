(** Maps between chosen limits, their functorial laws, and the natural
    comparison along a left adjoint. All equalities are equalities of
    actual morphisms; no extensionality axiom or chosen functor category
    is needed in this file. *)

From DiazPark Require Import Category CategoryLimits CategoryAdjunction.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cone_map {C D : category} {F G : functor C D}
    (a : nat_trans F G) {v : D} (s : cone F v) : cone G v.
Proof.
  refine {| cone_leg := fun x => compose (cone_leg s x) (component a x) |}.
  intros x y f.
  change (compose (compose (cone_leg s x) (component a x)) (fmap G f) =
    compose (cone_leg s y) (component a y)).
  rewrite compose_assoc, <- (naturality a f), <- compose_assoc.
  rewrite (cone_natural s f). reflexivity.
Defined.

Arguments cone_map {C D F G} a {v} s.

Definition cone_precompose {C D : category} {F : functor C D}
    {v w : D} (f : hom D v w) (s : cone F w) : cone F v.
Proof.
  refine {| cone_leg := fun x => compose f (cone_leg s x) |}.
  intros x y u. rewrite compose_assoc, (cone_natural s u). reflexivity.
Defined.

Lemma limit_hom_ext {C D : category} {F : functor C D}
    (K : limiting_cone F) {v : D} (f g : hom D v (limit_object K))
    (h : forall x, compose f (cone_leg (limit_cone K) x) =
      compose g (cone_leg (limit_cone K) x)) : f = g.
Proof.
  transitivity (limit_lift K (cone_precompose g (limit_cone K))).
  - apply limit_lift_unique. exact h.
  - symmetry. apply limit_lift_unique. intro x. reflexivity.
Qed.

Arguments limit_hom_ext {C D F} K {v} f g h.

Definition limit_map {C D : category} {F G : functor C D}
    (K : limiting_cone F) (J : limiting_cone G) (a : nat_trans F G) :
    hom D (limit_object K) (limit_object J) :=
  limit_lift J (cone_map a (limit_cone K)).

Arguments limit_map {C D F G} K J a.

Lemma limit_map_fac {C D : category} {F G : functor C D}
    (K : limiting_cone F) (J : limiting_cone G) (a : nat_trans F G) (x : C) :
    compose (limit_map K J a) (cone_leg (limit_cone J) x) =
      compose (cone_leg (limit_cone K) x) (component a x).
Proof. exact (limit_lift_fac J (cone_map a (limit_cone K)) x). Qed.

Lemma limit_map_id {C D : category} {F : functor C D} (K : limiting_cone F) :
    limit_map K K (nat_id F) = identity (limit_object K).
Proof.
  apply (limit_hom_ext K). intro x.
  rewrite limit_map_fac, compose_id_left.
  apply compose_id_right.
Qed.

Lemma limit_map_comp {C D : category} {F G H : functor C D}
    (K : limiting_cone F) (J : limiting_cone G) (I : limiting_cone H)
    (a : nat_trans F G) (b : nat_trans G H) :
    compose (limit_map K J a) (limit_map J I b) =
      limit_map K I (nat_comp a b).
Proof.
  apply (limit_hom_ext I). intro x.
  rewrite compose_assoc, (limit_map_fac J I b x), <- compose_assoc,
    (limit_map_fac K J a x), (limit_map_fac K I (nat_comp a b) x).
  apply compose_assoc.
Qed.

Lemma limit_map_congr {C D : category} {F G : functor C D}
    (K : limiting_cone F) (J : limiting_cone G) (a b : nat_trans F G)
    (h : forall x, component a x = component b x) :
    limit_map K J a = limit_map K J b.
Proof.
  apply (limit_hom_ext J). intro x.
  rewrite !limit_map_fac, (h x). reflexivity.
Qed.

(** Evaluation at the initial object computes not just the limit object
    but the map induced by every natural transformation of diagrams. *)
Lemma initial_limit_map {C D : category} {F G : functor C D}
    (i : initial_object C) (a : nat_trans F G) :
    limit_map (initial_limit F i) (initial_limit G i) a =
      component a (initial_point i).
Proof.
  change (compose (fmap F (initial_arrow i (initial_point i)))
    (component a (initial_point i)) = component a (initial_point i)).
  rewrite initial_arrow_self, fmap_id. apply compose_id_left.
Qed.

Lemma contravariant_terminal_limit_map {C D : category}
    {F G : functor (opposite C) D} (t : terminal_object C) (a : nat_trans F G) :
    limit_map (contravariant_terminal_limit F t)
      (contravariant_terminal_limit G t) a = component a (terminal_point t).
Proof. exact (initial_limit_map (terminal_initial_op t) a). Qed.

Definition limit_unique_iso {C D : category} {F : functor C D}
    (K J : limiting_cone F) : isomorphism (limit_object K) (limit_object J).
Proof.
  refine {| iso_hom := limit_map K J (nat_id F);
            iso_inv := limit_map J K (nat_id F) |}.
  - rewrite limit_map_comp.
    transitivity (limit_map K K (nat_id F)).
    + apply limit_map_congr. intro x. apply compose_id_left.
    + apply limit_map_id.
  - rewrite limit_map_comp.
    transitivity (limit_map J J (nat_id F)).
    + apply limit_map_congr. intro x. apply compose_id_left.
    + apply limit_map_id.
Defined.

Definition limit_restrict_map {B C D : category} (L : functor B C)
    {F : functor C D} (K : limiting_cone F)
    (J : limiting_cone (functor_comp L F)) :
    hom D (limit_object K) (limit_object J) :=
  limit_lift J (cone_restrict L (limit_cone K)).

Arguments limit_restrict_map {B C D} L {F} K J.

Lemma limit_restrict_map_fac {B C D : category} (L : functor B C)
    {F : functor C D} (K : limiting_cone F)
    (J : limiting_cone (functor_comp L F)) (x : B) :
    compose (limit_restrict_map L K J) (cone_leg (limit_cone J) x) =
      cone_leg (limit_cone K) (fobj L x).
Proof. exact (limit_lift_fac J (cone_restrict L (limit_cone K)) x). Qed.

(** This square is natural in the coefficient diagram without assuming
    that restriction is along an adjoint. *)
Lemma limit_restrict_map_natural {B C D : category} (L : functor B C)
    {F G : functor C D} (K : limiting_cone F) (J : limiting_cone G)
    (KL : limiting_cone (functor_comp L F))
    (JL : limiting_cone (functor_comp L G)) (a : nat_trans F G) :
    compose (limit_map K J a) (limit_restrict_map L J JL) =
      compose (limit_restrict_map L K KL)
        (limit_map KL JL (nat_whisker_left L a)).
Proof.
  apply (limit_hom_ext JL). intro x.
  rewrite !compose_assoc, limit_restrict_map_fac, !limit_map_fac.
  rewrite <- compose_assoc, limit_restrict_map_fac.
  exact (limit_map_fac K J a (fobj L x)).
Qed.

Definition left_adjoint_limit_iso {C D E : category}
    {L : functor C D} {R : functor D C} (a : adjunction L R)
    (F : functor D E) (K : limiting_cone F)
    (J : limiting_cone (functor_comp L F)) :
    isomorphism (limit_object K) (limit_object J) :=
  limit_unique_iso K (left_adjoint_limit a F J).

Arguments left_adjoint_limit_iso {C D E L R} a F K J.

Lemma left_adjoint_limit_iso_hom {C D E : category}
    {L : functor C D} {R : functor D C} (a : adjunction L R)
    (F : functor D E) (K : limiting_cone F)
    (J : limiting_cone (functor_comp L F)) :
    iso_hom (left_adjoint_limit_iso a F K J) = limit_restrict_map L K J.
Proof.
  apply (limit_hom_ext J). intro x.
  change (compose (limit_map K (left_adjoint_limit a F J) (nat_id F))
    (cone_leg (limit_cone J) x) =
    compose (limit_restrict_map L K J) (cone_leg (limit_cone J) x)).
  rewrite limit_restrict_map_fac.
  transitivity (compose (limit_map K (left_adjoint_limit a F J) (nat_id F))
    (cone_leg (limit_cone (left_adjoint_limit a F J)) (fobj L x))).
  - apply f_equal. symmetry.
    exact (adjunction_cone_restrict_extend a F (limit_cone J) x).
  - rewrite limit_map_fac. apply compose_id_right.
Qed.

(** The actual isomorphism obtained from the adjunction has the canonical
    restriction map as its forward map and is coefficient-natural. *)
Lemma left_adjoint_limit_iso_natural {C D E : category}
    {L : functor C D} {R : functor D C} (a : adjunction L R)
    (F G : functor D E) (K : limiting_cone F) (J : limiting_cone G)
    (KL : limiting_cone (functor_comp L F))
    (JL : limiting_cone (functor_comp L G)) (t : nat_trans F G) :
    compose (limit_map K J t) (iso_hom (left_adjoint_limit_iso a G J JL)) =
      compose (iso_hom (left_adjoint_limit_iso a F K KL))
        (limit_map KL JL (nat_whisker_left L t)).
Proof.
  rewrite !left_adjoint_limit_iso_hom.
  apply limit_restrict_map_natural.
Qed.
