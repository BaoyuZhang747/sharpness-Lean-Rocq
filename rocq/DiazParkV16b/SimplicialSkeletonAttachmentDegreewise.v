From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplicialSet SimplicialSubcomplex
  SimplicialSkeletonAttachmentCover.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSurjectiveFunctionDescent.

Section Descent.
Context {E D Z : Type} (q : E -> D) (hq : forall d, exists e, q e = d).
Variable a : E -> Z.

Definition chosen_preimage d : E := proj1_sig (cid (hq d)).
Lemma chosen_preimage_spec d : q (chosen_preimage d) = d.
Proof. exact (proj2_sig (cid (hq d))). Qed.

Definition descend_function d : Z := a (chosen_preimage d).

Lemma descend_function_fac (ha : forall e e', q e = q e' -> a e = a e') e :
  descend_function (q e) = a e.
Proof. apply ha. exact (chosen_preimage_spec (q e)). Qed.

Lemma descend_function_unique (b : D -> Z) (hb : forall e, b (q e) = a e) :
  b = descend_function.
Proof.
  apply functional_extensionality_dep. intro d.
  rewrite <- (chosen_preimage_spec d) at 1. exact (hb (chosen_preimage d)).
Qed.

End Descent.
End DPSurjectiveFunctionDescent.

Module DPSimplicialAttachmentDegreewise.
Import DPSimplicialSet DPSimplicialSubcomplex DPSimplicialAttachmentCover
  DPSurjectiveFunctionDescent.

Section Degree.
Context (X : simplicial_set) (n k : nat) (Z : Type).
Variable a : simplex (stage_set X n) k -> Z.
Variable b : simplex (cell_copower X n) k -> Z.
Variable w : forall c : simplex (boundary_copower X n) k,
  a (component (attaching_map X n) k c) =
  b (component (attaching_inclusion X n) k c).

Definition attaching_values (x : attaching_domain X n k) : Z :=
  match x with inl y => a y | inr y => b y end.

Lemma attaching_values_compatible (x y : attaching_domain X n k) :
  attaching_cover_map x = attaching_cover_map y -> attaching_values x = attaching_values y.
Proof.
  destruct x as [x|x], y as [y|y]; cbn; intro e.
  - apply f_equal. apply subcomplex_simplex_ext. exact (f_equal (@proj1_sig _ _) e).
  - destruct (@attaching_cells_into_old X n k y x (esym e)) as [c [hi ha]].
    rewrite <- hi. rewrite <- ha. exact (w c).
  - destruct (@attaching_cells_into_old X n k x y e) as [c [hi ha]].
    rewrite <- hi. rewrite <- ha. symmetry. exact (w c).
  - destruct (@attaching_cells_fiber X n k x y e) as [h|[c [d [hc [hd h]]]]].
    + rewrite h. reflexivity.
    + exact (eq_trans (f_equal b (esym hc))
        (eq_trans (esym (w c))
          (eq_trans (f_equal a h) (eq_trans (w d) (f_equal b hd))))).
Qed.

Definition attaching_degree_desc : simplex (stage_set X n.+1) k -> Z :=
  @descend_function _ _ _ (@attaching_cover_map X n k)
    (@attaching_cover_surjective X n k) attaching_values.

Lemma attaching_degree_desc_old (x : simplex (stage_set X n) k) :
  attaching_degree_desc (component (attaching_stage X n) k x) = a x.
Proof. exact (@descend_function_fac _ _ _ (@attaching_cover_map X n k)
  (@attaching_cover_surjective X n k) attaching_values attaching_values_compatible (inl x)). Qed.

Lemma attaching_degree_desc_cell (x : simplex (cell_copower X n) k) :
  attaching_degree_desc (component (attaching_cells X n) k x) = b x.
Proof. exact (@descend_function_fac _ _ _ (@attaching_cover_map X n k)
  (@attaching_cover_surjective X n k) attaching_values attaching_values_compatible (inr x)). Qed.

Lemma attaching_degree_desc_unique (d : simplex (stage_set X n.+1) k -> Z)
    (ha : forall x, d (component (attaching_stage X n) k x) = a x)
    (hb : forall x, d (component (attaching_cells X n) k x) = b x) :
  d = attaching_degree_desc.
Proof.
  apply descend_function_unique. intros [x|x]; [exact (ha x)|exact (hb x)].
Qed.

End Degree.
End DPSimplicialAttachmentDegreewise.
