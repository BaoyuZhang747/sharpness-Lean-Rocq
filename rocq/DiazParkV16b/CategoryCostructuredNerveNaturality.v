(** Literal postcomposition compatibility of the actual endpoint chart. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryReindex CategoryComma.
From DiazParkV16b Require Import SimplexCategory SimplicialSet CategoryNerve CategoryCostructuredDiagram CategoryCostructuredNerveEndpoint.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplexCategory DPSimplicialSet DPCategoryNerve DPCategoryCostructuredDiagram DPCategoryCostructuredNerveEndpoint.
Module DPCategoryCostructuredNerveNaturality.
Section Naturality.
Variables C D : category.
Variable T : functor C D.
Variables d e : D.
Variable f : hom D d e.
Variable n : nat.
Variable c : simplex (nerve C) n.
Variable a : hom D (fobj T (fobj c ord_max)) d.
Lemma endpoint_reindex_object i :
 fobj (functor_comp (@endpoint_simplex C D T d n c a) (reindex T f)) i=
 fobj (@endpoint_simplex C D T e n c (compose a f)) i.
Proof.
change (@Build_costructured_object C D T e (fobj c i) (compose (compose (fmap T (final_arrow c i)) a) f)=
 @Build_costructured_object C D T e (fobj c i) (compose (fmap T (final_arrow c i)) (compose a f))).
by rewrite compose_assoc.
Qed.
Theorem endpoint_reindex :
 functor_comp (@endpoint_simplex C D T d n c a) (reindex T f)=
 @endpoint_simplex C D T e n c (compose a f).
Proof.
apply (@functor_ext_pointwise _ _ _ _ endpoint_reindex_object).
move=>i j u; apply costructured_hom_ext; rewrite comma_transport_map.
change (hom_transport (f_equal costructured_source (endpoint_reindex_object i))
 (f_equal costructured_source (endpoint_reindex_object j)) (fmap c u)=fmap c u).
exact: hom_transport_loop.
Qed.
End Naturality.
End DPCategoryCostructuredNerveNaturality.
