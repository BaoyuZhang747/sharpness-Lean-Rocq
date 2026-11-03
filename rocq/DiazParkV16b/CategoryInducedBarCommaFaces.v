(** The Yoneda-defined induced boundary has precisely the ordinary face
    formula on the actual structured-comma strings. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryComma CategoryStructured CategoryModules
  CategoryModuleLinear BarPaths BarFreeModule BarCofaces BarComplex BarResolutionComparison.
From DiazParkV16b Require Import CategoryBarPullbackPaths CategoryInducedBarTerms
  CategoryInducedBarHom CategoryInducedBarDifferential CategoryInducedBarCommaPaths.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule DiazParkBarCofaces
  DiazParkBarComplex DiazParkBarResolutionComparison DPCategoryBarPullback.
Local Open Scope ring_scope.

Section Faces.
Variable R : pzRingType.
Variables C D : category.
Variable q : functor C D.
Variable d : D.

Lemma induced_bar_comma_face_generator n i
    (s : @path (structured_category q d) n.+1) :
    @induced_bar_generator_value R C D q (induced_bar_term R q n) n.+1
      (bar_coface (D := functor_comp (functor_op q) (induced_bar_term R q n)) i
        (induced_bar_to_cochain q (nat_id (induced_bar_term R q n)))) d
      (induced_bar_comma_to_basis q s) =
    free_basis R (induced_bar_comma_to_basis q (@path_face (structured_category q d) n i s)).
Proof.
destruct s as [[c a] t]; destruct i as [|i].
- destruct t as [[e b] [f v]].
  have hf := structured_commutes f.
  change (free_map R (@induced_bar_precompose C D q n d (fobj q c) a)
    (free_map R (@induced_bar_precompose C D q n (fobj q c) (fobj q e)
      (fmap q (structured_map f)))
      (free_basis R (existT _ (existT _ e
        (path_map_from (structured_projection q d) n (structured_point q e b) v))
        (identity (fobj q e))))) =
    free_basis R (existT _ (existT _ e
      (path_map_from (structured_projection q d) n (structured_point q e b) v)) b)).
  rewrite !free_map_basis /induced_bar_precompose compose_id_right.
  by rewrite hf.
- change (free_map R (@induced_bar_precompose C D q n d (fobj q c) a)
    (free_basis R (existT _ (existT _ c
      (@path_inner_face C n i c
        (path_map_from (structured_projection q d) n.+1 (structured_point q c a) t)))
      (identity (fobj q c)))) =
    free_basis R (existT _ (existT _ c
      (path_map_from (structured_projection q d) n (structured_point q c a)
        (@path_inner_face (structured_category q d) n i (structured_point q c a) t))) a)).
  rewrite free_map_basis /induced_bar_precompose compose_id_right.
  by rewrite path_map_inner_face.
Qed.

Lemma induced_bar_comma_boundary_generator n
    (s : @path (structured_category q d) n.+1) :
    module_hom_fun (component (induced_bar_boundary R q n) d)
      (free_basis R (induced_bar_comma_to_basis q s)) =
    \sum_(i < n.+2) (-1) ^+ i *:
      free_basis R (induced_bar_comma_to_basis q (@path_face (structured_category q d) n i s)).
Proof.
rewrite induced_bar_boundary_generator bar_d_formula.
destruct s as [[c a] t].
change (module_hom_to_linear (fmap (induced_bar_term R q n) a)
  (@bar_evaluation R C (functor_comp (functor_op q) (induced_bar_term R q n))
    n.+1 c (path_map_from (structured_projection q d) n.+1 (structured_point q c a) t)
    (\sum_(i < n.+2) (-1) ^+ i *:
    bar_coface (D := functor_comp (functor_op q) (induced_bar_term R q n)) i
      (induced_bar_to_cochain q (nat_id (induced_bar_term R q n))))) =
    \sum_(i < n.+2) (-1) ^+ i *:
      free_basis R (induced_bar_comma_to_basis q
        (@path_face (structured_category q d) n i (existT _ (structured_point q c a) t)))).
rewrite !linear_sum.
apply eq_bigr; intros i _.
rewrite !linearZ.
apply f_equal.
exact (@induced_bar_comma_face_generator n i (existT _ (structured_point q c a) t)).
Qed.
End Faces.
