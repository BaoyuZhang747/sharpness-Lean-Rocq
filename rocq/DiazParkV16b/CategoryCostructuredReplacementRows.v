(** Actual row coordinates for the costructured bisimplicial replacement. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality CategoryReindex CategoryComma CategoryStructured.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve BisimplicialSet BisimplicialChains
 SimplicialReplacementTypes SimplicialReplacement CategoryCostructuredDiagram CategoryCostructuredNerveEndpoint CategoryStructuredNerveInitial.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve DPBisimplicialSet DPBisimplicialChains DPSimplicialReplacementTypes DPSimplicialReplacement DPCategoryCostructuredDiagram.
Module DPCategoryCostructuredReplacementRows.
Section Rows.
Variables C D : category.
Variable T : functor C D.
Local Notation F := (costructured_nerve_diagram T).
Definition row_anchor q (c : simplex (nerve C) q) := fobj T (fobj c ord_max).
Definition row_model q p := {c : simplex (nerve C) q & simplex (nerve (structured_category (functor_id D) (row_anchor c))) p}.
Definition row_forward p q (x : replacement_cell F p q) : row_model q p :=
 match x with existT d s => existT _ (DPCategoryCostructuredNerveEndpoint.projected_simplex s)
 (@DPCategoryStructuredNerveInitial.initial_simplex D _ p d (DPCategoryCostructuredNerveEndpoint.endpoint s)) end.
Definition row_backward q p (x : row_model q p) : replacement_cell F p q :=
 match x with existT c u => existT _ (DPCategoryStructuredNerveInitial.projected_simplex u)
 (@DPCategoryCostructuredNerveEndpoint.endpoint_simplex C D T _ q c (DPCategoryStructuredNerveInitial.initial u)) end.
Lemma row_model_transport q p (c c' : simplex (nerve C) q) (e:c=c')
 (u : simplex (nerve (structured_category (functor_id D) (row_anchor c))) p) :
 eq_rect c (fun v=>simplex (nerve (structured_category (functor_id D) (row_anchor v))) p) u c' e =
 eq_rect (row_anchor c) (fun a=>simplex (nerve (structured_category (functor_id D) a)) p) u (row_anchor c') (f_equal (@row_anchor q) e).
Proof. destruct e; reflexivity. Qed.
Lemma row_forward_backward q p (x : row_model q p) : row_forward (row_backward x)=x.
Proof.
case:x=>c u; rewrite /row_backward /row_forward.
pose e := @DPCategoryCostructuredNerveEndpoint.projected_endpoint_simplex C D T _ q c (DPCategoryStructuredNerveInitial.initial u).
apply eq_sigT_uncurried; exists e.
rewrite row_model_transport.
have he : f_equal (@row_anchor q) e=Logic.eq_refl (row_anchor c) by apply Prop_irrelevance.
rewrite he /= DPCategoryCostructuredNerveEndpoint.endpoint_endpoint_simplex.
exact: DPCategoryStructuredNerveInitial.initial_simplex_inverse.
Qed.
Lemma row_backward_forward p q (x : replacement_cell F p q) : row_backward (row_forward x)=x.
Proof.
case:x=>d s; rewrite /row_backward /row_forward.
pose e := @DPCategoryStructuredNerveInitial.projected_initial_simplex D _ p d (DPCategoryCostructuredNerveEndpoint.endpoint s).
apply (@cell_equal D F p q _ _ e).
have he : f_equal (@DPSimplicialReplacementTypes.initial_object D p) e=Logic.eq_refl (fobj d ord0) by apply Prop_irrelevance.
rewrite he /= DPCategoryStructuredNerveInitial.initial_initial_simplex.
exact: DPCategoryCostructuredNerveEndpoint.endpoint_simplex_inverse.
Qed.
End Rows.
End DPCategoryCostructuredReplacementRows.
