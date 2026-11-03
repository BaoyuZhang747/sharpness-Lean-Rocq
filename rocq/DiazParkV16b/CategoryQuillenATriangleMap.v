(** The actual diagonal replacement simplex as a string in the varying comma. *)
From mathcomp Require Import all_ssreflect boolp.
From DiazPark Require Import Category CategoryComma CategoryReindex CategoryIsomorphism CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda
  CategoryNerve BisimplicialSet SimplicialReplacementTypes SimplicialReplacement
  CategoryCostructuredDiagram CategoryCostructuredNerveEndpoint CategoryQuillenATotalComma.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve
  DPBisimplicialSet DPSimplicialReplacementTypes DPSimplicialReplacement DPCategoryCostructuredDiagram
  DPCategoryCostructuredNerveEndpoint DPCategoryQuillenATotalComma.

Module DPCategoryQuillenATriangleMap.
Section Map.
Variables C D : category.
Variable T : functor C D.
Local Notation E := (total_category T).
Local Notation F := (costructured_nerve_diagram T).

Lemma initial_arrow_compose n (s : simplex (nerve D) n) i j (a : hom (ordinal_category n) i j) :
  compose (initial_arrow s i) (fmap s a) = initial_arrow s j.
Proof.
rewrite /initial_arrow -fmap_compose.
have he : @compose (ordinal_category n) ord0 i j (leq0n i) a = leq0n j.
  cbn; apply Prop_irrelevance.
exact (f_equal (@fmap _ _ s ord0 j) he).
Qed.

Definition cell_object n (s : simplex (nerve D) n)
    (a : simplex (nerve (costructured_category T (initial_object s))) n) (i : 'I_n.+1) : E :=
  @Build_total_object C D T (costructured_source (fobj a i)) (fobj s i)
    (compose (costructured_arrow (fobj a i)) (initial_arrow s i)).
Arguments cell_object {n} s a i.

Definition cell_arrow n (s : simplex (nerve D) n)
    (a : simplex (nerve (costructured_category T (initial_object s))) n)
    i j (u : hom (ordinal_category n) i j) : hom E (cell_object s a i) (cell_object s a j).
Proof.
refine (@Build_total_hom C D T (cell_object s a i) (cell_object s a j)
  (costructured_map (fmap a u)) (fmap s u) _).
change (compose (fmap T (costructured_map (fmap a u)))
  (compose (costructured_arrow (fobj a j)) (initial_arrow s j)) =
  compose (compose (costructured_arrow (fobj a i)) (initial_arrow s i)) (fmap s u)).
by rewrite -compose_assoc (costructured_commutes (fmap a u)) compose_assoc initial_arrow_compose.
Defined.
Arguments cell_arrow {n} s a {i j} u.

Definition cell_simplex n (s : simplex (nerve D) n)
    (a : simplex (nerve (costructured_category T (initial_object s))) n) : simplex (nerve E) n.
Proof.
refine (@Build_functor (ordinal_category n) E (cell_object s a) (fun i j u => cell_arrow s a u) _ _).
- move=>i; apply total_hom_ext; cbn.
  + rewrite fmap_id; reflexivity.
  + exact: fmap_id.
- move=>i j k u v; apply total_hom_ext; cbn.
  + rewrite fmap_compose; reflexivity.
  + exact: fmap_compose.
Defined.
Arguments cell_simplex {n} s a.

Lemma cell_object_pull n m (f : ordinal_map n m) (s : simplex (nerve D) m)
    (a : simplex (nerve (costructured_category T (initial_object s))) m) i :
  cell_object (simplex_map (nerve D) f s)
    (functor_comp (functor_comp (ordinal_functor f) a) (reindex T (initial_arrow s (f ord0)))) i =
  cell_object s a (f i).
Proof.
change (@Build_total_object C D T (costructured_source (fobj a (f i))) (fobj s (f i))
  (compose (compose (costructured_arrow (fobj a (f i))) (initial_arrow s (f ord0)))
    (initial_arrow (simplex_map (nerve D) f s) i)) =
  @Build_total_object C D T (costructured_source (fobj a (f i))) (fobj s (f i))
    (compose (costructured_arrow (fobj a (f i))) (initial_arrow s (f i)))).
apply object_arrow_eq; by rewrite compose_assoc initial_arrow_pull.
Qed.
Arguments cell_object_pull {n m} f s a i.

Lemma cell_simplex_pull n m (f : ordinal_map n m) (s : simplex (nerve D) m)
    (a : simplex (nerve (costructured_category T (initial_object s))) m) :
  cell_simplex (simplex_map (nerve D) f s)
    (functor_comp (functor_comp (ordinal_functor f) a) (reindex T (initial_arrow s (f ord0)))) =
  functor_comp (ordinal_functor f) (cell_simplex s a).
Proof.
apply (@functor_ext_pointwise (ordinal_category n) E
  (cell_simplex (simplex_map (nerve D) f s)
    (functor_comp (functor_comp (ordinal_functor f) a) (reindex T (initial_arrow s (f ord0)))))
  (functor_comp (ordinal_functor f) (cell_simplex s a)) (cell_object_pull f s a)).
move=> i j u; apply total_hom_ext.
- rewrite source_transport.
  change (hom_transport (f_equal (source (T := T)) (cell_object_pull f s a i))
    (f_equal (source (T := T)) (cell_object_pull f s a j))
    (costructured_map (fmap a (ordinal_monotone f u))) = costructured_map (fmap a (ordinal_monotone f u))).
  exact: hom_transport_loop.
- rewrite target_transport.
  change (hom_transport (f_equal (target (T := T)) (cell_object_pull f s a i))
    (f_equal (target (T := T)) (cell_object_pull f s a j))
    (fmap s (ordinal_monotone f u)) = fmap s (ordinal_monotone f u)).
  exact: hom_transport_loop.
Qed.

Definition diagonal_to_comma : simplicial_map (diagonal (replacement F)) (nerve E).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category (diagonal (replacement F)) (nerve E)
  (fun n x => cell_simplex (projT1 x) (projT2 x)) _).
move=> n m f; apply type_morphism_ext=> [[s a]].
exact: cell_simplex_pull.
Defined.

Lemma cell_source_projection n (s : simplex (nerve D) n)
    (a : simplex (nerve (costructured_category T (initial_object s))) n) :
  functor_comp (cell_simplex s a) (source_projection T) = projected_simplex a.
Proof.
apply (@functor_extensionality (ordinal_category n) C
  (functor_comp (cell_simplex s a) (source_projection T)) (projected_simplex a) Logic.eq_refl).
reflexivity.
Qed.

Lemma cell_target_projection n (s : simplex (nerve D) n)
    (a : simplex (nerve (costructured_category T (initial_object s))) n) :
  functor_comp (cell_simplex s a) (target_projection T) = s.
Proof.
apply (@functor_extensionality (ordinal_category n) D
  (functor_comp (cell_simplex s a) (target_projection T)) s Logic.eq_refl).
reflexivity.
Qed.
End Map.
End DPCategoryQuillenATriangleMap.
