(** Actual simplicial replacement cells and all-ordinal operations. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve BisimplicialSet.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve DPBisimplicialSet.
Module DPSimplicialReplacementTypes.
Section Replacement.
Variable C : category.
Variable F : functor C simplicial_category.
Definition initial_object p (s : simplex (nerve C) p) : C := fobj s ord0.
Definition initial_arrow p (s : simplex (nerve C) p) (i : 'I_p.+1) : hom C (initial_object s) (fobj s i) := @fmap _ _ s ord0 i (leq0n i).
Lemma initial_arrow_identity p (s : simplex (nerve C) p) : initial_arrow s ord0=identity (initial_object s).
Proof.
change (@fmap (ordinal_category p) C s ord0 ord0 (leq0n 0)=identity (fobj s ord0)).
have he : leq0n 0=leqnn (val (ord0 : 'I_p.+1)) by apply Prop_irrelevance.
rewrite he; exact (fmap_id s ord0).
Qed.
Lemma initial_arrow_pull p m (f : ordinal_map p m) (s : simplex (nerve C) m)
    (i : 'I_p.+1) :
  compose (initial_arrow s (f ord0))
    (initial_arrow (simplex_map (nerve C) f s) i) = initial_arrow s (f i).
Proof.
change (compose (@fmap _ _ s ord0 (f ord0) (leq0n (val (f ord0))))
  (@fmap _ _ s (f ord0) (f i) (@ordinal_monotone p m f ord0 i (leq0n (val i)))) =
  @fmap _ _ s ord0 (f i) (leq0n (val (f i)))).
rewrite -fmap_compose.
congr (@fmap (ordinal_category m) C s ord0 (f i) _).
change (leq_trans (leq0n (val (f ord0))) (@ordinal_monotone p m f ord0 i (leq0n (val i))) =
  leq0n (val (f i))).
apply Prop_irrelevance.
Qed.
Definition replacement_cell p q := {s : simplex (nerve C) p & simplex (fobj F (initial_object s)) q}.
Definition replacement_horizontal p m (f : ordinal_map p m) q (x : replacement_cell m q) : replacement_cell p q :=
 match x with existT s a => existT _ (simplex_map (nerve C) f s)
 (component (fmap F (initial_arrow s (f ord0))) q a) end.
Definition replacement_vertical p q n (g : ordinal_map q n) (x : replacement_cell p n) : replacement_cell p q :=
 match x with existT s a => existT _ s (simplex_map (fobj F (initial_object s)) g a) end.
Lemma cell_transport p q (s t : simplex (nerve C) p) (e : s=t)
 (x : simplex (fobj F (initial_object s)) q) :
 eq_rect s (fun v => simplex (fobj F (initial_object v)) q) x t e =
 eq_rect (initial_object s) (fun c => simplex (fobj F c) q) x (initial_object t) (f_equal (@initial_object p) e).
Proof. destruct e; reflexivity. Qed.
Lemma cell_equal p q (s t : simplex (nerve C) p) (e : s=t)
 (x : simplex (fobj F (initial_object s)) q) (y : simplex (fobj F (initial_object t)) q) :
 eq_rect (initial_object s) (fun c => simplex (fobj F c) q) x (initial_object t) (f_equal (@initial_object p) e)=y ->
 @existT _ (fun v => simplex (fobj F (initial_object v)) q) s x=existT _ t y.
Proof.
move=> h; apply eq_sigT_uncurried; exists e; by rewrite cell_transport.
Qed.
Lemma replacement_vertical_identity p q (x : replacement_cell p q) :
 replacement_vertical (ordinal_map_identity q) x=x.
Proof. case:x=>s a; rewrite /replacement_vertical simplex_map_identity; reflexivity. Qed.
Lemma replacement_vertical_compose p q n k (g : ordinal_map q n) (h : ordinal_map n k) (x : replacement_cell p k) :
 replacement_vertical (ordinal_map_compose g h) x=replacement_vertical g (replacement_vertical h x).
Proof. case:x=>s a; rewrite /replacement_vertical simplex_map_compose; reflexivity. Qed.
Lemma replacement_mixed p m (f : ordinal_map p m) q n (g : ordinal_map q n) (x : replacement_cell m n) :
 replacement_horizontal f (replacement_vertical g x)=replacement_vertical g (replacement_horizontal f x).
Proof.
case:x=>s a; rewrite /replacement_vertical /replacement_horizontal.
congr (existT _ _ _); exact: simplicial_map_naturality.
Qed.
Lemma replacement_horizontal_identity p q (x : replacement_cell p q) :
 replacement_horizontal (ordinal_map_identity p) x=x.
Proof.
case:x=>s a; rewrite /replacement_horizontal.
pose e := @simplex_map_identity (nerve C) p s.
apply (@cell_equal p q _ _ e).
have he : f_equal (@initial_object p) e=Logic.eq_refl (initial_object s) by apply Prop_irrelevance.
rewrite he /= initial_arrow_identity fmap_id; reflexivity.
Qed.
Lemma replacement_horizontal_compose p m k (f : ordinal_map p m) (g : ordinal_map m k)
    q (x : replacement_cell k q) :
  replacement_horizontal (ordinal_map_compose f g) x =
  replacement_horizontal f (replacement_horizontal g x).
Proof.
case: x=>s a; rewrite /replacement_horizontal.
pose e := @simplex_map_compose (nerve C) p m k f g s.
apply (@cell_equal p q _ _ e).
have he : f_equal (@initial_object p) e = Logic.eq_refl (fobj s (g (f ord0)))
  by apply Prop_irrelevance.
rewrite he /= -(initial_arrow_pull g s (f ord0)) fmap_compose; reflexivity.
Qed.
End Replacement.
End DPSimplicialReplacementTypes.
