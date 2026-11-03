(** Genuine replacement cells are category strings with a simplex at the source. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category BarPaths.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve
  CategoryNervePaths SimplicialReplacementTypes.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkBarPaths DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve
  DPCategoryNervePathEquivalence DPSimplicialReplacementTypes.

Module DPSimplicialReplacementDualCells.
Section Cells.
Variable C : category.
Variable F : functor C simplicial_category.

Definition string_cell p q := {c : C & (@path_from C p c * simplex (fobj F c) q)%type}.
Definition string_cell_path p q (a : string_cell p q) : @path C p :=
  match a with existT c (t,_) => existT _ c t end.
Definition cell_to_string p q (a : replacement_cell F p q) : string_cell p q :=
  match a with existT s x => existT _ (initial_object s) (nerve_path_from s,x) end.

Lemma cell_to_string_injective p q : injective (@cell_to_string p q).
Proof.
move=> [s x] [t y] h.
have hs : s=t.
  apply nerve_path_injective; exact (f_equal (@string_cell_path p q) h).
subst t.
have hp := @existT_inj2 [the eqType of classicType C]
  (fun c => (@path_from C p c * simplex (fobj F c) q)%type) (initial_object s) _ _ h.
have hx : x=y := f_equal (@snd _ _) hp.
by subst y.
Qed.

Lemma cell_preimage_of_path p q (s : simplex (nerve C) p) (t : @path C p)
  (h : nerve_path s=t) (x : simplex (fobj F (path_source t)) q) :
  exists a : replacement_cell F p q, cell_to_string a = existT _ (path_source t) (projT2 t,x).
Proof.
destruct h; exists (existT _ s x); reflexivity.
Qed.

Lemma cell_to_string_surjective p q (a : string_cell p q) :
  exists b, cell_to_string b=a.
Proof.
case: a => c [t x].
exact (@cell_preimage_of_path p q (path_nerve (existT _ c t)) (existT _ c t)
  (nerve_path_nerve (existT _ c t)) x).
Qed.

Definition string_to_cell p q (a : string_cell p q) : replacement_cell F p q :=
  proj1_sig (constructive_indefinite_description (cell_to_string_surjective a)).
Lemma cell_string_inverse p q (a : string_cell p q) : cell_to_string (string_to_cell a)=a.
Proof. exact (proj2_sig (constructive_indefinite_description (cell_to_string_surjective a))). Qed.
Lemma string_cell_inverse p q (a : replacement_cell F p q) : string_to_cell (cell_to_string a)=a.
Proof. apply cell_to_string_injective; exact: cell_string_inverse. Qed.

Lemma cell_to_string_formula p q (s : simplex (nerve C) p) (x : simplex (fobj F (initial_object s)) q) :
  cell_to_string (existT _ s x) = existT _ (initial_object s) (nerve_path_from s,x).
Proof. reflexivity. Qed.
End Cells.
End DPSimplicialReplacementDualCells.
