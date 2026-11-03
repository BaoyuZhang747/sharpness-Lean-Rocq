(** The dual maps and universal-property constructions needed by left Kan
    extensions. These use arbitrary categories and no additional axioms. *)

From DiazPark Require Import Category CategoryLimits.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition cocone_map {C D : category} {F G : functor C D}
    (a : nat_trans F G) {v : D} (s : cocone G v) : cocone F v.
Proof.
  refine {| cocone_leg := fun x => compose (component a x) (cocone_leg s x) |}.
  intros x y f.
  change (compose (fmap F f) (compose (component a y) (cocone_leg s y)) =
    compose (component a x) (cocone_leg s x)).
  rewrite <- compose_assoc, (naturality a f), compose_assoc.
  rewrite (cocone_natural s f). reflexivity.
Defined.

Definition cocone_postcompose {C D : category} {F : functor C D}
    {v w : D} (s : cocone F v) (f : hom D v w) : cocone F w.
Proof.
  refine {| cocone_leg := fun x => compose (cocone_leg s x) f |}.
  intros x y u. rewrite <- compose_assoc, (cocone_natural s u). reflexivity.
Defined.

Lemma colimit_hom_ext {C D : category} {F : functor C D}
    (K : colimiting_cocone F) {v : D} (f g : hom D (colimit_object K) v)
    (h : forall x, compose (cocone_leg (colimit_cocone K) x) f =
      compose (cocone_leg (colimit_cocone K) x) g) : f = g.
Proof.
  transitivity (colimit_desc K (cocone_postcompose (colimit_cocone K) g)).
  - apply colimit_desc_unique. exact h.
  - symmetry. apply colimit_desc_unique. intro x. reflexivity.
Qed.

Arguments colimit_hom_ext {C D F} K {v} f g h.

Definition colimit_map {C D : category} {F G : functor C D}
    (K : colimiting_cocone F) (J : colimiting_cocone G) (a : nat_trans F G) :
    hom D (colimit_object K) (colimit_object J) :=
  colimit_desc K (cocone_map a (colimit_cocone J)).

Lemma colimit_map_fac {C D : category} {F G : functor C D}
    (K : colimiting_cocone F) (J : colimiting_cocone G) (a : nat_trans F G) (x : C) :
    compose (cocone_leg (colimit_cocone K) x) (colimit_map K J a) =
      compose (component a x) (cocone_leg (colimit_cocone J) x).
Proof. exact (colimit_desc_fac K (cocone_map a (colimit_cocone J)) x). Qed.

Lemma colimit_map_id {C D : category} {F : functor C D}
    (K : colimiting_cocone F) :
    colimit_map K K (nat_id F) = identity (colimit_object K).
Proof.
  apply (colimit_hom_ext K). intro x.
  rewrite colimit_map_fac, compose_id_right. apply compose_id_left.
Qed.

Lemma colimit_map_comp {C D : category} {F G H : functor C D}
    (K : colimiting_cocone F) (J : colimiting_cocone G) (I : colimiting_cocone H)
    (a : nat_trans F G) (b : nat_trans G H) :
    compose (colimit_map K J a) (colimit_map J I b) =
      colimit_map K I (nat_comp a b).
Proof.
  apply (colimit_hom_ext K). intro x.
  rewrite <- compose_assoc, (colimit_map_fac K J a x), compose_assoc,
    (colimit_map_fac J I b x), (colimit_map_fac K I (nat_comp a b) x).
  symmetry. apply compose_assoc.
Qed.

Lemma colimit_map_congr {C D : category} {F G : functor C D}
    (K : colimiting_cocone F) (J : colimiting_cocone G) (a b : nat_trans F G)
    (h : forall x, component a x = component b x) :
    colimit_map K J a = colimit_map K J b.
Proof.
  apply (colimit_hom_ext K). intro x.
  rewrite !colimit_map_fac, (h x). reflexivity.
Qed.

Definition colimit_unique_iso {C D : category} {F : functor C D}
    (K J : colimiting_cocone F) : isomorphism (colimit_object K) (colimit_object J).
Proof.
  refine {| iso_hom := colimit_map K J (nat_id F);
            iso_inv := colimit_map J K (nat_id F) |}.
  - rewrite colimit_map_comp.
    transitivity (colimit_map K K (nat_id F)).
    + apply colimit_map_congr. intro x. apply compose_id_left.
    + apply colimit_map_id.
  - rewrite colimit_map_comp.
    transitivity (colimit_map J J (nat_id F)).
    + apply colimit_map_congr. intro x. apply compose_id_left.
    + apply colimit_map_id.
Defined.

Lemma terminal_colimit_map {C D : category} {F G : functor C D}
    (t : terminal_object C) (a : nat_trans F G) :
    colimit_map (terminal_colimit F t) (terminal_colimit G t) a =
      component a (terminal_point t).
Proof.
  change (compose (component a (terminal_point t))
    (fmap G (terminal_arrow t (terminal_point t))) = component a (terminal_point t)).
  rewrite terminal_arrow_self, fmap_id. apply compose_id_right.
Qed.

Definition cone_op {C D : category} {F : functor C D}
    {v : D} (s : cone F v) : cocone (functor_op F) v.
Proof.
  refine (@Build_cocone (opposite C) (opposite D) (functor_op F) v
    (cone_leg s) _).
  intros x y f. exact (cone_natural s f).
Defined.

Definition cocone_op {C D : category} {F : functor C D}
    {v : D} (s : cocone F v) : cone (functor_op F) v.
Proof.
  refine (@Build_cone (opposite C) (opposite D) (functor_op F) v
    (cocone_leg s) _).
  intros x y f. exact (cocone_natural s f).
Defined.

(** Reverse conversions are explicit, so they do not require equality
    of a category/functor record with its double opposite. *)
Definition cone_unop {C D : category} {F : functor C D}
    {v : D} (s : cone (functor_op F) v) : cocone F v.
Proof.
  refine (@Build_cocone C D F v (cone_leg s) _).
  intros x y f. exact (cone_natural s f).
Defined.

Definition cocone_unop {C D : category} {F : functor C D}
    {v : D} (s : cocone (functor_op F) v) : cone F v.
Proof.
  refine (@Build_cone C D F v (cocone_leg s) _).
  intros x y f. exact (cocone_natural s f).
Defined.

Definition limit_op {C D : category} {F : functor C D}
    (K : limiting_cone F) : colimiting_cocone (functor_op F).
Proof.
  refine (@Build_colimiting_cocone (opposite C) (opposite D) (functor_op F)
    (limit_object K) (cone_op (limit_cone K))
    (fun v s => limit_lift K (cocone_unop s)) _ _).
  - intros v s x. exact (limit_lift_fac K (cocone_unop s) x).
  - intros v s f h. exact (limit_lift_unique K (cocone_unop s) f h).
Defined.

Definition colimit_op {C D : category} {F : functor C D}
    (K : colimiting_cocone F) : limiting_cone (functor_op F).
Proof.
  refine (@Build_limiting_cone (opposite C) (opposite D) (functor_op F)
    (colimit_object K) (cocone_op (colimit_cocone K))
    (fun v s => colimit_desc K (cone_unop s)) _ _).
  - intros v s x. exact (colimit_desc_fac K (cone_unop s) x).
  - intros v s f h. exact (colimit_desc_unique K (cone_unop s) f h).
Defined.
