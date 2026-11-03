From mathcomp Require Import all_ssreflect order boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory
  SimplexCategoryFactorization SimplexCategoryFactorizationSections
  SimplexCategoryFactorizationProperties SimplicialSet SimplicialSetYoneda
  SimplicialSubcomplex SimplicialSubcomplexGenerated SimplicialSkeleton
  SimplicialNondegenerate SimplicialNondegenerateUniqueness
  SimplicialNondegenerateSkeleton SimplicialBoundary SimplicialCopower
  SimplicialSkeletonAttachmentStages.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialAttachmentCover.
Import DPSimplicialTypes DPSimplexCategory DPSimplexFactorization DPSimplexSections
  DPSimplexFactorizationProperties DPSimplicialSet DPSimplicialYoneda
  DPSimplicialSubcomplex DPSimplicialGenerated DPSimplicialSkeleton
  DPSimplicialNondegenerate DPSimplicialNondegenerateUniqueness
  DPSimplicialNondegenerateSkeleton DPSimplicialBoundary DPSimplicialCopower
  DPSimplicialAttachmentStages.

Definition stage_set X n := subcomplex_set (skeletal_stage X n).
Definition cell_copower X n := copower (nondegenerate_cell X n) (standard_simplex n).
Definition boundary_copower X n := copower (nondegenerate_cell X n) (boundary_set n).

Definition attaching_inclusion X n : simplicial_map (boundary_copower X n) (cell_copower X n) :=
  @copower_map (nondegenerate_cell X n) _ _ (boundary_inclusion n).
Definition attaching_map X n : simplicial_map (boundary_copower X n) (stage_set X n) :=
  copower_desc (@cell_boundary_characteristic X n).
Definition attaching_cells X n : simplicial_map (cell_copower X n) (stage_set X n.+1) :=
  copower_desc (@cell_characteristic X n).
Definition attaching_stage X n : simplicial_map (stage_set X n) (stage_set X n.+1) :=
  subcomplex_map (@skeletal_stage_mono X n).

Lemma attaching_square X n :
  nat_comp (attaching_inclusion X n) (attaching_cells X n) =
    nat_comp (attaching_map X n) (attaching_stage X n).
Proof.
  apply nat_trans_ext. intro k. apply type_morphism_ext. intros [x f].
  apply subcomplex_simplex_ext. reflexivity.
Qed.

Definition attaching_domain X n k :=
  (simplex (stage_set X n) k + simplex (cell_copower X n) k)%type.

Definition attaching_cover_map X n k (x : attaching_domain X n k) :
    simplex (stage_set X n.+1) k :=
  match x with
  | inl a => component (attaching_stage X n) k a
  | inr b => component (attaching_cells X n) k b
  end.

Theorem attaching_cover_surjective X n k (x : simplex (stage_set X n.+1) k) :
  exists y : attaching_domain X n k, attaching_cover_map y = x.
Proof.
  destruct x as [x hx].
  destruct (@nondegenerate_core_exists X k x) as [m [q [y [hq [hy he]]]]].
  have hm : (m <= n)%N.
  { apply (proj1 (@core_skeletal_stage_iff X n.+1 k m q hq y hy)).
    rewrite he. exact hx. }
  rewrite leq_eqVlt in hm. move/orP: hm => [/eqP e|hm].
  - subst m. exists (inr (exist _ y hy,q)). apply subcomplex_simplex_ext. exact he.
  - have hold : member (skeletal_stage X n) k x.
    { rewrite <- he. exact (proj2 (@core_skeletal_stage_iff X n k m q hq y hy) hm). }
    exists (inl (exist _ x hold)). apply subcomplex_simplex_ext. reflexivity.
Qed.

Lemma attaching_cells_into_old X n k (b : simplex (cell_copower X n) k)
    (a : simplex (stage_set X n) k)
    (e : component (attaching_cells X n) k b = component (attaching_stage X n) k a) :
  exists c : simplex (boundary_copower X n) k,
    component (attaching_inclusion X n) k c = b /\
    component (attaching_map X n) k c = a.
Proof.
  destruct b as [[y hy] f], a as [a ha].
  have ev : simplex_map X f y = a := f_equal (@proj1_sig _ _) e.
  have hf : ~ ordinal_surjective f.
  { apply (proj1 (@nondegenerate_characteristic_below_iff X n k y hy f)).
    rewrite ev. exact ha. }
  exists (exist _ y hy, exist _ f hf). split; first reflexivity.
  apply subcomplex_simplex_ext. exact ev.
Qed.

Lemma attaching_cells_fiber X n k (b c : simplex (cell_copower X n) k)
    (e : component (attaching_cells X n) k b = component (attaching_cells X n) k c) :
  b = c \/ exists a a' : simplex (boundary_copower X n) k,
    component (attaching_inclusion X n) k a = b /\
    component (attaching_inclusion X n) k a' = c /\
    component (attaching_map X n) k a = component (attaching_map X n) k a'.
Proof.
  destruct b as [[y hy] f], c as [[z hz] g].
  have ev : simplex_map X f y = simplex_map X g z := f_equal (@proj1_sig _ _) e.
  destruct (pselect (ordinal_surjective f)) as [hf|hf].
  - left. destruct (@nondegenerate_core_same_dimension_unique X k n f hf g y z hy ev)
      as [ef ey]. subst g z. f_equal. f_equal. apply Prop_irrelevance.
  - right. have hg : ~ ordinal_surjective g.
    { apply (proj1 (@nondegenerate_characteristic_below_iff X n k z hz g)).
      rewrite <- ev. exact (@boundary_characteristic_below X n k y f hf). }
    exists (exist _ y hy, exist _ f hf), (exist _ z hz, exist _ g hg).
    split; first reflexivity. split; first reflexivity.
    apply subcomplex_simplex_ext. exact ev.
Qed.

End DPSimplicialAttachmentCover.
