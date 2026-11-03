From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialSubcomplex.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPSimplicialGenerated.
Import DPSimplexCategory DPSimplicialSet DPSimplicialSubcomplex.

Section Generated.
Variable X : simplicial_set.
Variable P : forall n, simplex X n -> Prop.

(** Closure under all ordinal maps is described by actual generator images. *)
Definition generated_member n (x : simplex X n) : Prop :=
  exists k (y : simplex X k) (f : ordinal_map n k),
    @P k y /\ simplex_map X f y = x.

Definition generated_subcomplex : subcomplex X.
Proof.
  refine (@Subcomplex X generated_member _).
  intros n m f x [k [y [g [hy hx]]]].
  exists k, y, (ordinal_map_compose f g). split; first exact hy.
  rewrite simplex_map_compose hx. reflexivity.
Defined.

Lemma generated_contains n (x : simplex X n) :
  @P n x -> member generated_subcomplex n x.
Proof.
  intro hx. exists n, x, (ordinal_map_identity n). split; first exact hx.
  apply simplex_map_identity.
Qed.

Lemma generated_le (S : subcomplex X) :
  subcomplex_le generated_subcomplex S <->
    (forall n x, @P n x -> member S n x).
Proof.
  split.
  - intros h n x hx. apply h. exact (generated_contains hx).
  - intros h n x [k [y [f [hy e]]]].
    subst x. exact (member_closed S f y (h k y hy)).
Qed.

End Generated.

Arguments generated_subcomplex {_} _.

Lemma generated_mono X (P Q : forall n, simplex X n -> Prop) :
  (forall n x, @P n x -> @Q n x) ->
    subcomplex_le (generated_subcomplex P) (generated_subcomplex Q).
Proof.
  intros h n x [k [y [f [hy e]]]].
  exists k, y, f. split; [exact (h k y hy)|exact e].
Qed.

Lemma generated_subcomplex_self X (S : subcomplex X) :
  generated_subcomplex (fun n x => member S n x) = S.
Proof.
  apply subcomplex_le_antisymm.
  - apply (proj2 (@generated_le X (fun n x => member S n x) S)).
    intros n x hx. exact hx.
  - intros n x hx. apply generated_contains. exact hx.
Qed.

Lemma generated_singleton_member X n (x : simplex X n) k (y : simplex X k) :
  member (generated_subcomplex
    (fun m z => exists (f : ordinal_map m n), simplex_map X f x = z)) k y <->
    exists f : ordinal_map k n, simplex_map X f x = y.
Proof.
  split.
  - intros [m [z [f [[g hg] he]]]].
    exists (ordinal_map_compose f g). rewrite simplex_map_compose hg. exact he.
  - intro h. apply generated_contains. exact h.
Qed.

End DPSimplicialGenerated.
