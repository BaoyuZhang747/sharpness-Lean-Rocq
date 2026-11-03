(** Recover the actual mapped pushout from the colimit of the mapped span. *)
From DiazPark Require Import Category CategoryLimits.
From DiazParkV16b Require Import CategoryPushout.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPCategoryPushoutColimit.
Import DPCategoryPushout.
Section MappedSpan.
Context {C D : category} (F : functor C D) {A B X : C}
  (i : hom C A B) (j : hom C A X).
Variable K : colimiting_cocone (functor_comp (span_diagram i j) F).

Definition mapped_span_cocone {Z : D}
  (a : hom D (fobj F B) Z) (b : hom D (fobj F X) Z)
  (w : compose (fmap F i) a = compose (fmap F j) b) :
  cocone (functor_comp (span_diagram i j) F) Z.
Proof.
  refine (@Build_cocone span_category D (functor_comp (span_diagram i j) F) Z
    (fun s => match s with span_source => compose (fmap F i) a
       | span_left => a | span_right => b end) _).
  intros x y f; destruct x,y; cbn in *; try contradiction;
    try (rewrite fmap_id; apply compose_id_left); try reflexivity.
  symmetry; exact w.
Defined.

Definition mapped_span_colimit_pushout :
  pushout_square (fmap F i) (fmap F j)
    (cocone_leg (colimit_cocone K) span_left)
    (cocone_leg (colimit_cocone K) span_right).
Proof.
  refine (@Build_pushout_square D _ _ _ _ _ _ _ _ _
    (fun Z a b w => colimit_desc K (@mapped_span_cocone Z a b w)) _ _ _).
  - transitivity (cocone_leg (colimit_cocone K) span_source).
    + exact (@cocone_natural _ _ _ _ (colimit_cocone K) span_source span_left I).
    + symmetry. exact (@cocone_natural _ _ _ _ (colimit_cocone K) span_source span_right I).
  - intros Z a b w. exact (colimit_desc_fac K (@mapped_span_cocone Z a b w) span_left).
  - intros Z a b w. exact (colimit_desc_fac K (@mapped_span_cocone Z a b w) span_right).
  - intros Z a b w d hd1 hd2. apply colimit_desc_unique.
    intro s; destruct s; cbn; [|exact hd1|exact hd2].
    rewrite <- (@cocone_natural _ _ _ _ (colimit_cocone K) span_source span_left I).
    rewrite compose_assoc. change (compose (fmap F i)
      (compose (cocone_leg (colimit_cocone K) span_left) d) = compose (fmap F i) a).
    exact (f_equal (fun z : hom D (fobj F B) Z => compose (fmap F i) z) hd1).
Defined.
End MappedSpan.
End DPCategoryPushoutColimit.
