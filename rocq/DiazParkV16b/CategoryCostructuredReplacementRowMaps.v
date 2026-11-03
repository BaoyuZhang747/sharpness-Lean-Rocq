(** The actual row coordinate bijection is a simplicial isomorphism. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality CategoryReindex CategoryComma CategoryStructured.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve BisimplicialSet BisimplicialChains
 SimplicialReplacementTypes SimplicialReplacement CategoryCostructuredDiagram CategoryCostructuredNerveEndpoint CategoryStructuredNerveInitial CategoryCostructuredNerveNaturality CategoryCostructuredReplacementRows.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve DPBisimplicialSet DPBisimplicialChains DPSimplicialReplacementTypes DPSimplicialReplacement DPCategoryCostructuredDiagram DPCategoryCostructuredReplacementRows.
Module DPCategoryCostructuredReplacementRowMaps.
Section RowMaps.
Variables C D : category.
Variable T : functor C D.
Variable q : nat.
Local Notation F := (costructured_nerve_diagram T).
Definition row_model_set : simplicial_set.
Proof.
refine (@Build_functor (opposite simplex_category) type_category (fun p=>row_model T q p)
 (fun p m f x=>match x with existT c u=>existT _ c (simplex_map _ f u) end) _ _).
- move=>p; apply type_morphism_ext=>[[c u]]; rewrite simplex_map_identity; reflexivity.
- move=>p m k f g; apply type_morphism_ext=>[[c u]]; rewrite simplex_map_compose; reflexivity.
Defined.
Lemma row_backward_natural p m (f : ordinal_map p m) (x : row_model T q m) :
 row_backward (simplex_map row_model_set f x)=horizontal_map (replacement F) f q (row_backward x).
Proof.
case:x=>c u.
change (@existT (simplex (nerve D) p) (fun v=>simplex (fobj F (initial_object v)) q) (functor_comp (functor_comp (ordinal_functor f) u) (structured_projection (functor_id D) (row_anchor T c)))
 (@DPCategoryCostructuredNerveEndpoint.endpoint_simplex C D T _ q c (structured_arrow (fobj u (f ord0)))) =
 existT _ (functor_comp (ordinal_functor f) (DPCategoryStructuredNerveInitial.projected_simplex u))
 (functor_comp (@DPCategoryCostructuredNerveEndpoint.endpoint_simplex C D T _ q c (DPCategoryStructuredNerveInitial.initial u))
 (reindex T (initial_arrow (DPCategoryStructuredNerveInitial.projected_simplex u) (f ord0))))).
pose e := @functor_comp_assoc _ _ _ _ (ordinal_functor f) u (structured_projection (functor_id D) (row_anchor T c)).
apply (@cell_equal D F p q _ _ e).
have he : f_equal (@initial_object D p) e=Logic.eq_refl (structured_source (fobj u (f ord0))) by apply Prop_irrelevance.
rewrite he /= DPCategoryCostructuredNerveNaturality.endpoint_reindex.
have h := structured_commutes (@fmap _ _ u ord0 (f ord0) (leq0n (val (f ord0)))).
change (compose (DPCategoryStructuredNerveInitial.initial u)
 (initial_arrow (DPCategoryStructuredNerveInitial.projected_simplex u) (f ord0))=structured_arrow (fobj u (f ord0))) in h.
by rewrite h.
Qed.
Definition row_backward_map : simplicial_map row_model_set (horizontal_simplicial (replacement F) q).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category row_model_set (horizontal_simplicial (replacement F) q)
 (fun p=>@row_backward C D T q p) _).
move=>p m f; apply type_morphism_ext=>x; exact: row_backward_natural.
Defined.
Lemma row_backward_injective p : injective (@row_backward C D T q p).
Proof. move=>x y h; rewrite -(row_forward_backward x) -(row_forward_backward y) h; reflexivity. Qed.
Definition row_forward_map : simplicial_map (horizontal_simplicial (replacement F) q) row_model_set.
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (horizontal_simplicial (replacement F) q) row_model_set
 (fun p=>@row_forward C D T p q) _).
move=>p m f; apply type_morphism_ext=>x; apply row_backward_injective.
change (row_backward (row_forward (horizontal_map (replacement F) f q x))=
 row_backward (simplex_map row_model_set f (row_forward x))).
by rewrite row_backward_natural !row_backward_forward.
Defined.
Definition row_isomorphism : @isomorphism simplicial_category (horizontal_simplicial (replacement F) q) row_model_set.
Proof.
refine (@Build_isomorphism simplicial_category _ _ row_forward_map row_backward_map _ _).
- apply nat_trans_ext=>p; apply type_morphism_ext=>x; exact: row_backward_forward.
- apply nat_trans_ext=>p; apply type_morphism_ext=>x; exact: row_forward_backward.
Defined.
End RowMaps.
End DPCategoryCostructuredReplacementRowMaps.
