(** The replacement-cell chart preserves both actual face operations. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category BarPaths.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplicialSet SimplicialSetOperators
  SimplicialSetYoneda CategoryNerve CategoryNervePathsPrefix CategoryNervePaths CategoryNervePathsFacesOrdinal
  CategoryNervePathsFaces SimplicialReplacementTypes SimplicialReplacementDualCells.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkBarPaths DPSimplexCategory DPSimplexOperators DPSimplicialSet DPSimplicialOperators
  DPSimplicialYoneda DPCategoryNerve DPCategoryNervePaths DPCategoryNervePathEquivalence
  DPCategoryNerveFaceOrdinal DPCategoryNervePathFaces DPSimplicialReplacementTypes DPSimplicialReplacementDualCells.

Module DPSimplicialReplacementDualFaces.
Section Faces.
Variable C : category.
Variable F : functor C simplicial_category.

Definition string_horizontal_face p q i (a : string_cell F p.+1 q) : string_cell F p q :=
  match a with existT c (t,x) =>
    match i with
    | 0 => match t with existT d (f,r) => existT _ d (r,component (fmap F f) q x) end
    | j.+1 => existT _ c (@path_inner_face C p j c t,x)
    end
  end.
Definition string_vertical p q n (g : ordinal_map q n) (a : string_cell F p n) : string_cell F p q :=
  match a with existT c (t,x) => existT _ c (t,simplex_map (fobj F c) g x) end.

Lemma cell_chart_vertical p q n (g : ordinal_map q n) (a : replacement_cell F p n) :
  cell_to_string (replacement_vertical g a) = string_vertical g (cell_to_string a).
Proof. by case: a => s x. Qed.

Lemma cell_chart_horizontal_zero p q (a : replacement_cell F p.+1 q) :
  cell_to_string (replacement_horizontal (@coface p ord0) a) = string_horizontal_face 0 (cell_to_string a).
Proof.
case: a => s x; rewrite coface_zero_shift; reflexivity.
Qed.

Lemma cell_chart_horizontal_successor p q (i : 'I_p.+1) (a : replacement_cell F p.+1 q) :
  cell_to_string (replacement_horizontal (coface (shift_vertex i)) a) = string_horizontal_face i.+1 (cell_to_string a).
Proof.
case: a => s x; rewrite coface_successor_normalized /replacement_horizontal /cell_to_string.
change (existT (fun c => (@path_from C p c * simplex (fobj F c) q)%type) (initial_object s)
  (nerve_path_from (simplex_map (nerve C) (positive_coface i) s),
    component (fmap F (initial_arrow s ord0)) q x) =
  existT _ (initial_object s) (@path_inner_face C p (val i) (initial_object s) (nerve_path_from s),x)).
rewrite initial_arrow_identity fmap_id.
have h := @nerve_path_face C p (shift_vertex i) s.
rewrite /face coface_successor_normalized in h.
have hv : val (shift_vertex i) = (val i).+1 by destruct i; reflexivity.
rewrite hv in h.
change (existT (fun c => @path_from C p c) (initial_object s)
  (nerve_path_from (simplex_map (nerve C) (positive_coface i) s)) =
  existT _ (initial_object s) (@path_inner_face C p (val i) (initial_object s) (nerve_path_from s))) in h.
have hp := @existT_inj2 [the eqType of classicType C] (fun c => @path_from C p c) (initial_object s) _ _ h.
by rewrite hp.
Qed.

Lemma cell_chart_horizontal p q (i : 'I_p.+2) (a : replacement_cell F p.+1 q) :
  cell_to_string (replacement_horizontal (coface i) a) = string_horizontal_face (val i) (cell_to_string a).
Proof.
case: i => [[|i] hi].
- have e : @Ordinal p.+2 0 hi = ord0 by apply val_inj; reflexivity.
  rewrite e; exact: cell_chart_horizontal_zero.
- have e : @Ordinal p.+2 i.+1 hi = shift_vertex (@Ordinal p.+1 i hi) by apply val_inj; reflexivity.
  rewrite e; exact: cell_chart_horizontal_successor.
Qed.
End Faces.
End DPSimplicialReplacementDualFaces.
