From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryLimits CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet
  SimplicialSetYoneda SimplicialSubcomplex CategoryPushout
  SimplicialSkeletonAttachmentCover SimplicialSkeletonAttachmentDegreewise.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialAttachmentPushout.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda
  DPSimplicialSubcomplex DPCategoryPushout DPSimplicialAttachmentCover
  DPSimplicialAttachmentDegreewise.

Section Descent.
Context (X : simplicial_set) (n : nat) (Y : simplicial_set).
Variable a : simplicial_map (stage_set X n) Y.
Variable b : simplicial_map (cell_copower X n) Y.
Variable w : nat_comp (attaching_inclusion X n) b = nat_comp (attaching_map X n) a.

Definition attachment_component k : simplex (stage_set X n.+1) k -> simplex Y k :=
  @attaching_degree_desc X n k (simplex Y k) (component a k) (component b k).

Lemma attachment_component_compat k (c : simplex (boundary_copower X n) k) :
  component a k (component (attaching_map X n) k c) =
    component b k (component (attaching_inclusion X n) k c).
Proof.
  symmetry. exact (f_equal
    (fun t : simplicial_map (boundary_copower X n) Y => component t k c) w).
Qed.

Lemma attachment_component_old k (x : simplex (stage_set X n) k) :
  attachment_component (component (attaching_stage X n) k x) = component a k x.
Proof. exact (@attaching_degree_desc_old X n k (simplex Y k)
  (component a k) (component b k) (@attachment_component_compat k) x). Qed.

Lemma attachment_component_cell k (x : simplex (cell_copower X n) k) :
  attachment_component (component (attaching_cells X n) k x) = component b k x.
Proof. exact (@attaching_degree_desc_cell X n k (simplex Y k)
  (component a k) (component b k) (@attachment_component_compat k) x). Qed.

Definition attachment_desc : simplicial_map (stage_set X n.+1) Y.
Proof.
  refine (@Build_nat_trans (opposite simplex_category) type_category
    (stage_set X n.+1) Y attachment_component _).
  intros m k f. apply type_morphism_ext. intro x.
  destruct (@attaching_cover_surjective X n m x) as [[u|v] e].
  - subst x.
    change (attachment_component (simplex_map (stage_set X n.+1) f
      (component (attaching_stage X n) m u)) =
      simplex_map Y f (attachment_component (component (attaching_stage X n) m u))).
    rewrite <- (simplicial_map_naturality (attaching_stage X n) f u).
    rewrite !attachment_component_old. exact (simplicial_map_naturality a f u).
  - subst x.
    change (attachment_component (simplex_map (stage_set X n.+1) f
      (component (attaching_cells X n) m v)) =
      simplex_map Y f (attachment_component (component (attaching_cells X n) m v))).
    rewrite <- (simplicial_map_naturality (attaching_cells X n) f v).
    rewrite !attachment_component_cell. exact (simplicial_map_naturality b f v).
Defined.

Lemma attachment_desc_old : nat_comp (attaching_stage X n) attachment_desc = a.
Proof. apply nat_trans_ext. intro k. apply type_morphism_ext. exact (@attachment_component_old k). Qed.

Lemma attachment_desc_cell : nat_comp (attaching_cells X n) attachment_desc = b.
Proof. apply nat_trans_ext. intro k. apply type_morphism_ext. exact (@attachment_component_cell k). Qed.

Lemma attachment_desc_unique (d : simplicial_map (stage_set X n.+1) Y)
    (ha : nat_comp (attaching_stage X n) d = a)
    (hb : nat_comp (attaching_cells X n) d = b) : d = attachment_desc.
Proof.
  apply nat_trans_ext. intro k. apply attaching_degree_desc_unique.
  - intro x. exact (f_equal
      (fun t : simplicial_map (stage_set X n) Y => component t k x) ha).
  - intro x. exact (f_equal
      (fun t : simplicial_map (cell_copower X n) Y => component t k x) hb).
Qed.

End Descent.

Definition skeletal_attachment_pushout X n :
  @pushout_square simplicial_category _ _ _ _
    (attaching_inclusion X n) (attaching_map X n)
    (attaching_cells X n) (attaching_stage X n).
Proof.
  refine (@Build_pushout_square simplicial_category _ _ _ _ _ _ _ _
    (attaching_square X n) (fun Y b a w => @attachment_desc X n Y a b w) _ _ _).
  - intros Y b a w. exact (@attachment_desc_cell X n Y a b w).
  - intros Y b a w. exact (@attachment_desc_old X n Y a b w).
  - intros Y b a w d hb ha. exact (@attachment_desc_unique X n Y a b w d ha hb).
Defined.

Definition skeletal_attachment_colimit X n :
  colimiting_cocone (@span_diagram simplicial_category _ _ _
    (attaching_inclusion X n) (attaching_map X n)) :=
  pushout_colimit (skeletal_attachment_pushout X n).

End DPSimplicialAttachmentPushout.
