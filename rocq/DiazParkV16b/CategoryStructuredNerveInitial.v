(** An under-category nerve simplex is determined by its base string and initial arrow. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality CategoryReindex CategoryComma CategoryStructured.
From DiazParkV16b Require Import SimplexCategory SimplicialSet CategoryNerve SimplicialReplacementTypes.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexCategory DPSimplicialSet DPCategoryNerve DPSimplicialReplacementTypes.
Module DPCategoryStructuredNerveInitial.
Section Initial.
Variable D : category.
Variable a : D.
Variable n : nat.
Local Notation U := (structured_category (functor_id D) a).
Definition initial_object (s : simplex (nerve D) n) (h : hom D a (fobj s ord0)) i : U :=
 structured_point (functor_id D) (fobj s i) (compose h (initial_arrow s i)).
Arguments initial_object s h i : clear implicits.
Definition initial_morphism (s : simplex (nerve D) n) (h : hom D a (fobj s ord0))
 i j (u : hom (ordinal_category n) i j) : hom U (initial_object s h i) (initial_object s h j).
Proof.
refine (@structured_morphism D D (functor_id D) a (initial_object s h i) (initial_object s h j) (fmap s u) _).
change (compose (compose h (initial_arrow s i)) (fmap s u)=compose h (initial_arrow s j)).
rewrite compose_assoc /initial_arrow -fmap_compose.
have e : @compose (ordinal_category n) ord0 i j (leq0n i) u=leq0n j.
 change (leq_trans (leq0n i) u=leq0n j); apply Prop_irrelevance.
by rewrite e.
Defined.
Arguments initial_morphism s h {i j} u.
Definition initial_simplex (s : simplex (nerve D) n) (h : hom D a (fobj s ord0)) : simplex (nerve U) n.
Proof.
refine (@Build_functor (ordinal_category n) U (initial_object s h) (fun i j u=>initial_morphism s h u) _ _).
- move=>i; apply costructured_hom_ext; exact: fmap_id.
- move=>i j k u v; apply costructured_hom_ext; exact: fmap_compose.
Defined.
Arguments initial_simplex s h : clear implicits.
Definition projected_simplex (s : simplex (nerve U) n) := functor_comp s (structured_projection (functor_id D) a).
Definition initial (s : simplex (nerve U) n) := structured_arrow (fobj s ord0).
Lemma initial_object_inverse (s : simplex (nerve U) n) i :
 initial_object (projected_simplex s) (initial s) i=fobj s i.
Proof.
have e := structured_commutes (@fmap _ _ s ord0 i (leq0n i)).
change (compose (initial s) (initial_arrow (projected_simplex s) i)=structured_arrow (fobj s i)) in e.
rewrite /initial_object e.
change (@Build_costructured_object (opposite D) (opposite D) (functor_op (functor_id D)) a
 (costructured_source (fobj s i)) (costructured_arrow (fobj s i))=fobj s i).
by case:(fobj s i).
Qed.
Lemma structured_transport_map (x y x' y' : U) (hx:x=x') (hy:y=y') (u:hom U x y) :
 structured_map (hom_transport hx hy u)=hom_transport (f_equal structured_source hx) (f_equal structured_source hy) (structured_map u).
Proof. destruct hx,hy; reflexivity. Qed.
Lemma initial_simplex_inverse (s : simplex (nerve U) n) : initial_simplex (projected_simplex s) (initial s)=s.
Proof.
apply (@functor_ext_pointwise _ _ (initial_simplex (projected_simplex s) (initial s)) s (initial_object_inverse s)).
move=>i j u; apply costructured_hom_ext.
change (structured_map (hom_transport (initial_object_inverse s i) (initial_object_inverse s j) (fmap (initial_simplex (projected_simplex s) (initial s)) u))=structured_map (fmap s u)).
rewrite structured_transport_map.
change (hom_transport (f_equal structured_source (initial_object_inverse s i))
 (f_equal structured_source (initial_object_inverse s j)) (structured_map (fmap s u))=structured_map (fmap s u)).
exact: hom_transport_loop.
Qed.
Lemma projected_initial_simplex s h : projected_simplex (initial_simplex s h)=s.
Proof.
apply (@functor_ext_pointwise _ _ (projected_simplex (initial_simplex s h)) s (fun i=>Logic.eq_refl _)).
move=>i j u; reflexivity.
Qed.
Lemma initial_initial_simplex s h : initial (initial_simplex s h)=h.
Proof.
change (compose h (initial_arrow s ord0)=h).
by rewrite initial_arrow_identity compose_id_right.
Qed.
End Initial.
End DPCategoryStructuredNerveInitial.
