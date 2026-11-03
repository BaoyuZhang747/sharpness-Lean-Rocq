(** The literal covariant nerve diagram d |-> N(T downarrow d). *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality CategoryReindex CategoryComma CategoryLeftKan.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplicialSet DPSimplicialYoneda DPCategoryNerve.
Module DPCategoryCostructuredDiagram.
Section Diagram.
Variables C D : category.
Variable T : functor C D.
Definition reindex d e (f : hom D d e) : functor (costructured_category T d) (costructured_category T e).
Proof.
refine (@Build_functor _ _ (costructured_reindex_object T f)
 (fun x y a => costructured_reindex_map T f a) _ _).
- move=>x; apply costructured_hom_ext; reflexivity.
- move=>x y z a b; apply costructured_hom_ext; reflexivity.
Defined.
Lemma reindex_object_id d (x : costructured_category T d) :
 fobj (reindex (identity d)) x=x.
Proof. case:x=>x h; rewrite /reindex /costructured_reindex_object /= compose_id_right; reflexivity. Qed.
Lemma reindex_object_comp d e k (f : hom D d e) (g : hom D e k) (x : costructured_category T d) :
 fobj (reindex (compose f g)) x=fobj (functor_comp (reindex f) (reindex g)) x.
Proof. case:x=>x h; rewrite /reindex /costructured_reindex_object /= compose_assoc; reflexivity. Qed.
Lemma comma_transport_map d (x y x' y' : costructured_category T d) (hx:x=x') (hy:y=y') (a:hom (costructured_category T d) x y) :
 costructured_map (hom_transport hx hy a)=hom_transport (f_equal costructured_source hx) (f_equal costructured_source hy) (costructured_map a).
Proof. destruct hx,hy; reflexivity. Qed.
Lemma reindex_id d : reindex (identity d)=functor_id (costructured_category T d).
Proof.
apply (@functor_ext_pointwise _ _ (reindex (identity d)) (functor_id (costructured_category T d)) (@reindex_object_id d)).
move=>x y a; apply costructured_hom_ext; rewrite comma_transport_map.
change (hom_transport (f_equal costructured_source (reindex_object_id x))
 (f_equal costructured_source (reindex_object_id y)) (costructured_map a)=costructured_map a).
exact: hom_transport_loop.
Qed.
Lemma reindex_comp d e k (f:hom D d e) (g:hom D e k) :
 reindex (compose f g)=functor_comp (reindex f) (reindex g).
Proof.
apply (@functor_ext_pointwise _ _ (reindex (compose f g)) (functor_comp (reindex f) (reindex g)) (@reindex_object_comp d e k f g)).
move=>x y a; apply costructured_hom_ext; rewrite comma_transport_map.
change (hom_transport (f_equal costructured_source (reindex_object_comp f g x))
 (f_equal costructured_source (reindex_object_comp f g y)) (costructured_map a)=costructured_map a).
exact: hom_transport_loop.
Qed.
Definition costructured_nerve_diagram : functor D simplicial_category.
Proof.
refine (@Build_functor D simplicial_category (fun d=>nerve (costructured_category T d))
 (fun d e f=>nerve_map (reindex f)) _ _).
- move=>d; apply nat_trans_ext=>n; apply type_morphism_ext=>s.
  change (functor_comp s (reindex (identity d))=s).
  by rewrite reindex_id functor_comp_id_right.
- move=>d e k f g; apply nat_trans_ext=>n; apply type_morphism_ext=>s.
  change (functor_comp s (reindex (compose f g))=functor_comp (functor_comp s (reindex f)) (reindex g)).
  by rewrite reindex_comp functor_comp_assoc.
Defined.
Definition costructured_projection_nerve d : simplicial_map (fobj costructured_nerve_diagram d) (nerve C) :=
 nerve_map (costructured_projection T d).
Lemma projection_reindex d e (f:hom D d e) :
 functor_comp (reindex f) (costructured_projection T e)=costructured_projection T d.
Proof.
apply (@functor_ext_pointwise _ _ (functor_comp (reindex f) (costructured_projection T e)) (costructured_projection T d) (fun x=>Logic.eq_refl _)).
move=>x y a; reflexivity.
Qed.
Lemma projection_nerve_natural d e (f:hom D d e) n s :
 component (costructured_projection_nerve e) n (component (fmap costructured_nerve_diagram f) n s)=
 component (costructured_projection_nerve d) n s.
Proof.
change (functor_comp (functor_comp s (reindex f)) (costructured_projection T e)=functor_comp s (costructured_projection T d)).
by rewrite functor_comp_assoc projection_reindex.
Qed.
End Diagram.
End DPCategoryCostructuredDiagram.
