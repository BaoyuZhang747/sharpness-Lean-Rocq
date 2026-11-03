(** A comma-nerve simplex is reconstructed from its projected string and final arrow. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality CategoryReindex CategoryComma.
From DiazParkV16b Require Import SimplexCategory SimplicialSet CategoryNerve CategoryCostructuredDiagram.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexCategory DPSimplicialSet DPCategoryNerve DPCategoryCostructuredDiagram.
Module DPCategoryCostructuredNerveEndpoint.
Section Endpoint.
Variables C D : category.
Variable T : functor C D.
Variable d : D.
Variable n : nat.
Definition final_arrow (s : simplex (nerve C) n) (i : 'I_n.+1) : hom C (fobj s i) (fobj s ord_max) :=
 @fmap _ _ s i ord_max (leq_ord i).
Lemma final_arrow_identity (s : simplex (nerve C) n) : final_arrow s ord_max=identity (fobj s ord_max).
Proof.
rewrite /final_arrow.
have e : leq_ord (ord_max : 'I_n.+1)=leqnn (val (ord_max : 'I_n.+1)) by apply Prop_irrelevance.
rewrite e; exact: fmap_id.
Qed.
Lemma final_arrow_compose (s : simplex (nerve C) n) i j (a : hom (ordinal_category n) i j) :
 compose (fmap s a) (final_arrow s j)=final_arrow s i.
Proof.
rewrite /final_arrow -fmap_compose.
have he : @compose (ordinal_category n) i j ord_max a (leq_ord j)=leq_ord i.
  change (leq_trans a (leq_ord j)=leq_ord i).
  apply Prop_irrelevance.
exact (f_equal (@fmap _ _ s i ord_max) he).
Qed.
Definition endpoint_object (s : simplex (nerve C) n) (a : hom D (fobj T (fobj s ord_max)) d) (i : 'I_n.+1) : costructured_category T d :=
 @Build_costructured_object C D T d (fobj s i) (compose (fmap T (final_arrow s i)) a).
Arguments endpoint_object s a i : clear implicits.
Definition endpoint_morphism (s : simplex (nerve C) n) (a : hom D (fobj T (fobj s ord_max)) d)
 i j (u : hom (ordinal_category n) i j) : hom (costructured_category T d) (endpoint_object s a i) (endpoint_object s a j).
Proof.
refine (@Build_costructured_hom C D T d (endpoint_object s a i) (endpoint_object s a j) (fmap s u) _).
change (compose (fmap T (fmap s u)) (compose (fmap T (final_arrow s j)) a)=compose (fmap T (final_arrow s i)) a).
by rewrite -compose_assoc -fmap_compose final_arrow_compose.
Defined.
Arguments endpoint_morphism s a {i j} u.
Definition endpoint_simplex (s : simplex (nerve C) n) (a : hom D (fobj T (fobj s ord_max)) d) : simplex (nerve (costructured_category T d)) n.
Proof.
refine (@Build_functor (ordinal_category n) (costructured_category T d) (endpoint_object s a)
 (fun i j u=>endpoint_morphism s a u) _ _).
- move=>i; apply costructured_hom_ext; exact: fmap_id.
- move=>i j k u v; apply costructured_hom_ext; exact: fmap_compose.
Defined.
Arguments endpoint_simplex s a : clear implicits.
Definition projected_simplex (s : simplex (nerve (costructured_category T d)) n) :=
 functor_comp s (costructured_projection T d).
Definition endpoint (s : simplex (nerve (costructured_category T d)) n) := costructured_arrow (fobj s ord_max).
Lemma endpoint_object_inverse (s : simplex (nerve (costructured_category T d)) n) i :
 endpoint_object (projected_simplex s) (endpoint s) i=fobj s i.
Proof.
have e := costructured_commutes (@fmap _ _ s i ord_max (leq_ord i)).
change (compose (fmap T (final_arrow (projected_simplex s) i)) (endpoint s)=costructured_arrow (fobj s i)) in e.
rewrite /endpoint_object e.
change (@Build_costructured_object C D T d (costructured_source (fobj s i)) (costructured_arrow (fobj s i))=fobj s i).
by case:(fobj s i).
Qed.
Lemma endpoint_simplex_inverse (s : simplex (nerve (costructured_category T d)) n) :
 endpoint_simplex (projected_simplex s) (endpoint s)=s.
Proof.
apply (@functor_ext_pointwise _ _ (endpoint_simplex (projected_simplex s) (endpoint s)) s (endpoint_object_inverse s)).
move=>i j u; apply costructured_hom_ext.
rewrite comma_transport_map.
change (hom_transport (f_equal costructured_source (endpoint_object_inverse s i))
 (f_equal costructured_source (endpoint_object_inverse s j)) (costructured_map (fmap s u))=costructured_map (fmap s u)).
exact: hom_transport_loop.
Qed.
Lemma projected_endpoint_simplex s a : projected_simplex (endpoint_simplex s a)=s.
Proof.
apply (@functor_ext_pointwise _ _ (projected_simplex (endpoint_simplex s a)) s (fun i=>Logic.eq_refl _)).
move=>i j u; reflexivity.
Qed.
Lemma endpoint_endpoint_simplex s a : endpoint (endpoint_simplex s a)=a.
Proof.
change (compose (fmap T (final_arrow s ord_max)) a=a).
by rewrite final_arrow_identity fmap_id compose_id_left.
Qed.
End Endpoint.
End DPCategoryCostructuredNerveEndpoint.
