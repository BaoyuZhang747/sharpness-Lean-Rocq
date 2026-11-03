From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  BarPaths BarFreeModule BarResolutionTerms BarResolutionFaces
  BarResolutionDifferential BarResolutionAugmentation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule
  DiazParkBarResolutionTerms DiazParkBarResolutionFaces
  DiazParkBarResolutionDifferential DiazParkBarResolutionAugmentation.
Local Open Scope ring_scope.

Module DiazParkBarResolutionContraction.
Section Contraction.
Variable R : pzRingType.
Variable C : category.

Definition resolution_insert n (x : C) (p : path_from (C := C) n.+1 x) :
    path_from (C := C) n.+2 x := existT _ x (@identity C x, p).

Lemma resolution_insert_face_zero n (x : C) (p : path_from (C := C) n.+1 x) :
  @path_inner_face C n.+1 0 x (resolution_insert p) = p.
Proof. case: p => y [f q]; by rewrite /resolution_insert /= compose_id_left. Qed.

Lemma resolution_insert_face_succ n i (x : C) (p : path_from (C := C) n.+2 x) :
  @path_inner_face C n.+2 i.+1 x (resolution_insert p) =
    resolution_insert (@path_inner_face C n.+1 i x p).
Proof. reflexivity. Qed.

Definition resolution_contraction n (x : C) :
    {linear resolution_term_obj (C := C) R n x -> resolution_term_obj (C := C) R n.+1 x} :=
  free_map R (@resolution_insert n x).

Lemma resolution_contraction_basis n (x : C) (p : path_from (C := C) n.+1 x) :
  resolution_contraction n x (free_basis R p) = free_basis R (resolution_insert p).
Proof. exact: free_map_basis. Qed.

Lemma resolution_contraction_face_zero n (x : C)
    (a : resolution_term_obj (C := C) R n x) :
  resolution_face_linear R n 0 x (resolution_contraction n x a) = a.
Proof.
apply: (free_lift_ext
  (g := (resolution_face_linear R n 0 x \o resolution_contraction n x :
    {linear resolution_term_obj (C := C) R n x -> resolution_term_obj (C := C) R n x}))
  (h := (idfun : {linear resolution_term_obj (C := C) R n x -> resolution_term_obj (C := C) R n x}))).
move=> p; rewrite /= resolution_contraction_basis /resolution_face_linear.
change (free_map R (@path_inner_face C n.+1 0 x)
  (free_basis R (resolution_insert p)) = free_basis R p).
by rewrite free_map_basis resolution_insert_face_zero.
Qed.

Lemma resolution_contraction_face_succ n i (x : C)
    (a : resolution_term_obj (C := C) R n.+1 x) :
  resolution_face_linear R n.+1 i.+1 x (resolution_contraction n.+1 x a) =
  resolution_contraction n x (resolution_face_linear R n i x a).
Proof.
apply: (free_lift_ext
  (g := (resolution_face_linear R n.+1 i.+1 x \o resolution_contraction n.+1 x :
    {linear resolution_term_obj (C := C) R n.+1 x -> resolution_term_obj (C := C) R n.+1 x}))
  (h := (resolution_contraction n x \o resolution_face_linear R n i x :
    {linear resolution_term_obj (C := C) R n.+1 x -> resolution_term_obj (C := C) R n.+1 x}))).
move=> p.
change (free_map R (@path_inner_face C n.+2 i.+1 x)
    (resolution_contraction n.+1 x (free_basis R p)) =
  resolution_contraction n x
    (free_map R (@path_inner_face C n.+1 i x) (free_basis R p))).
by rewrite resolution_contraction_basis !free_map_basis resolution_insert_face_succ.
Qed.

Theorem resolution_contraction_successor n (x : C)
    (a : resolution_term_obj (C := C) R n.+1 x) :
  @resolution_boundary_fun R C n.+1 x (resolution_contraction n.+1 x a) +
    resolution_contraction n x (@resolution_boundary_fun R C n x a) = a.
Proof.
rewrite /resolution_boundary_fun big_ord_recl expr0 scale1r
  resolution_contraction_face_zero linear_sum.
have he : \sum_(i < n.+2) (-1) ^+ i.+1 *:
    resolution_face_linear R n.+1 i.+1 x (resolution_contraction n.+1 x a) =
    - (\sum_(i < n.+2) resolution_contraction n x
      ((-1) ^+ i *: resolution_face_linear R n i x a)).
  rewrite -sumrN; apply: eq_bigr => i _.
  rewrite resolution_contraction_face_succ linearZ exprS mulN1r scaleNr.
  reflexivity.
rewrite he; exact: subrK.
Qed.

Lemma resolution_contraction_face_last (x : C)
    (a : resolution_term_obj (C := C) R 0 x) :
  resolution_face_linear R 0 1 x (resolution_contraction 0 x a) =
    @resolution_augmentation_section_fun R C x
      (@resolution_augmentation_fun R C x a).
Proof.
apply: (free_lift_ext
  (g := (resolution_face_linear R 0 1 x \o resolution_contraction 0 x :
    {linear resolution_term_obj (C := C) R 0 x -> resolution_term_obj (C := C) R 0 x}))
  (h := (@resolution_augmentation_section_fun R C x \o
    @resolution_augmentation_fun R C x :
    {linear resolution_term_obj (C := C) R 0 x -> resolution_term_obj (C := C) R 0 x}))).
move=> p.
change (resolution_face_linear R 0 1 x (resolution_contraction 0 x (free_basis R p)) =
  @resolution_augmentation_section_fun R C x
    (@resolution_augmentation_fun R C x (free_basis R p))).
rewrite resolution_contraction_basis resolution_augmentation_basis
  /resolution_augmentation_section_fun scale1r /resolution_face_linear.
change (free_map R (@path_inner_face C 1 1 x)
  (free_basis R (@resolution_insert 0 x p)) = free_basis R (existT _ x (@identity C x, tt))).
by rewrite free_map_basis; case: p => y [f []].
Qed.

Theorem resolution_contraction_zero (x : C)
    (a : resolution_term_obj (C := C) R 0 x) :
  @resolution_boundary_fun R C 0 x (resolution_contraction 0 x a) +
    @resolution_augmentation_section_fun R C x
      (@resolution_augmentation_fun R C x a) = a.
Proof.
rewrite /resolution_boundary_fun !big_ord_recl big_ord0 expr0 expr1
  scale1r scaleN1r resolution_contraction_face_zero resolution_contraction_face_last.
by rewrite addr0 subrK.
Qed.

Theorem resolution_exact_successor n (x : C)
    (a : resolution_term_obj (C := C) R n.+1 x) :
  @resolution_boundary_fun R C n x a = 0 ->
  exists b : resolution_term_obj (C := C) R n.+2 x,
    @resolution_boundary_fun R C n.+1 x b = a.
Proof.
move=> ha; exists (resolution_contraction n.+1 x a).
have h := resolution_contraction_successor a.
by rewrite ha linear0 addr0 in h.
Qed.

Theorem resolution_exact_zero (x : C)
    (a : resolution_term_obj (C := C) R 0 x) :
  @resolution_augmentation_fun R C x a = 0 ->
  exists b : resolution_term_obj (C := C) R 1 x,
    @resolution_boundary_fun R C 0 x b = a.
Proof.
move=> ha; exists (resolution_contraction 0 x a).
have h := resolution_contraction_zero a.
by rewrite ha linear0 addr0 in h.
Qed.

Theorem resolution_augmentation_surjective (x : C) (r : R^o) :
  exists a : resolution_term_obj (C := C) R 0 x,
    @resolution_augmentation_fun R C x a = r.
Proof.
exists (@resolution_augmentation_section_fun R C x r).
exact: resolution_augmentation_section.
Qed.

End Contraction.
End DiazParkBarResolutionContraction.


