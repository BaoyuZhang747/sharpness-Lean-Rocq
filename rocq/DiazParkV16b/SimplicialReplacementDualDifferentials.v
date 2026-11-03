(** The actual cell/bar module comparison commutes with both differentials. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear BarPaths BarCofaces BarComplex BarNaturality BarFreeModule.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryOperators SimplicialSet SimplicialSetYoneda
  SimplicialChains SimplicialChainsMaps LinearMapSpace BisimplicialSet BisimplicialChains
  SimplicialReplacement SimplicialReplacementTypes SimplicialReplacementDualCells
  SimplicialReplacementDualFaces SimplicialReplacementDualTerms CategoryCochainReplacementSimplicial.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkBarCofaces DiazParkBarComplex DiazParkBarNaturality DiazParkFreeModule
  DPSimplexCategory DPSimplexOperators DPSimplicialSet DPSimplicialYoneda DPSimplicialChains DPSimplicialChainMaps
  DPLinearMapSpace DPBisimplicialSet DPBisimplicialChains DPSimplicialReplacement DPSimplicialReplacementTypes
  DPSimplicialReplacementDualCells DPSimplicialReplacementDualFaces DPSimplicialReplacementDualTerms
  DPCategoryCochainReplacementSimplicial.
Local Open Scope ring_scope.

Module DPSimplicialReplacementDualDifferentials.
Section Differentials.
Variable R : comPzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable A : lmodType R.

Definition bar_value_hom p q (a : string_cell F p q) : module_hom (@bar_hom R C F A p q) A.
Proof. exists (fun f => bar_value f a); move=> r f g; exact: bar_value_linear. Defined.

Lemma bar_value_coface p q i (f : @bar_hom R C F A p q) (a : string_cell F p.+1 q) :
  bar_value (@bar_coface R C (dual_degree F A q) p i f) a = bar_value f (string_horizontal_face i a).
Proof.
case: i => [|i]; case: a => c [t x]; last reflexivity.
case: t => d [g t].
change (evaluate (f d t) (map_at R (fmap F g) q (free_basis R x)) =
  evaluate (f d t) (free_basis R (component (fmap F g) q x))).
by rewrite map_at_basis.
Qed.

Lemma bar_value_horizontal p q (f : @bar_hom R C F A p q) (a : string_cell F p.+1 q) :
  bar_value (bar_d (dual_degree F A q) p f) a =
    \sum_(i < p.+2) (-1:R)^+i *: bar_value f (string_horizontal_face (val i) a).
Proof.
change (bar_value_hom a (bar_d (dual_degree F A q) p f) =
  \sum_(i < p.+2) (-1:R)^+i *: bar_value f (string_horizontal_face (val i) a)).
rewrite bar_d_formula linear_sum; apply eq_bigr => i _.
rewrite linearZ; congr (_ *: _); exact: bar_value_coface.
Qed.

Lemma from_bar_horizontal p q (f : @bar_hom R C F A p q) :
  @precompose R (bi_term R (replacement F) p q) A (bi_term R (replacement F) p.+1 q) (@horizontal_d R (replacement F) p q) (from_bar f) =
    from_bar (bar_d (dual_degree F A q) p f).
Proof.
apply ext => a; apply (free_lift_ext
  (g := as_linear (@precompose R (bi_term R (replacement F) p q) A (bi_term R (replacement F) p.+1 q) (@horizontal_d R (replacement F) p q) (from_bar f)))
  (h := as_linear (from_bar (bar_d (dual_degree F A q) p f)))) => s.
change (evaluate (from_bar f) (@horizontal_d R (replacement F) p q (free_basis R s)) =
  evaluate (from_bar (bar_d (dual_degree F A q) p f)) (free_basis R s)).
rewrite from_bar_basis bar_value_horizontal /horizontal_d linear_sum.
apply eq_bigr => i _; rewrite linearZ map_at_basis.
change ((-1:R)^+i *: evaluate (from_bar f)
  (free_basis R (component (fmap (replacement F) (coface (inord (val i)))) q s)) =
  (-1:R)^+i *: bar_value f (string_horizontal_face (val i) (cell_to_string s))).
rewrite from_bar_basis.
congr (_ *: _); congr (bar_value f _).
change (cell_to_string (replacement_horizontal (coface (inord (val i))) s) =
  string_horizontal_face (val i) (cell_to_string s)).
rewrite cell_chart_horizontal; congr (string_horizontal_face _ _).
exact (@inordK p.+1 (val i) (ltn_ord i)).
Qed.

Lemma bar_value_vertical p q (f : @bar_hom R C F A p q) (a : string_cell F p q.+1) :
  bar_value (bar_map_at (dual_differential F A q) f) a =
    \sum_(i < q.+2) (-1:R)^+i *: bar_value f (string_vertical (coface (inord (val i))) a).
Proof.
case: a => c [t x].
change (evaluate (f c t) (@DPSimplicialChains.boundary R (fobj F c) q (free_basis R x)) =
  \sum_(i < q.+2) (-1:R)^+i *: evaluate (f c t)
    (free_basis R (simplex_map (fobj F c) (coface (inord (val i))) x))).
rewrite /DPSimplicialChains.boundary linear_sum; apply eq_bigr => i _.
by rewrite linearZ /face_map free_map_basis.
Qed.

Lemma from_bar_vertical p q (f : @bar_hom R C F A p q) :
  @precompose R (bi_term R (replacement F) p q) A (bi_term R (replacement F) p q.+1) (@vertical_d R (replacement F) p q) (from_bar f) =
    from_bar (bar_map_at (dual_differential F A q) f).
Proof.
apply ext => a; apply (free_lift_ext
  (g := as_linear (@precompose R (bi_term R (replacement F) p q) A (bi_term R (replacement F) p q.+1) (@vertical_d R (replacement F) p q) (from_bar f)))
  (h := as_linear (from_bar (bar_map_at (dual_differential F A q) f)))) => s.
change (evaluate (from_bar f) (@DPSimplicialChains.boundary R (fobj (replacement F) p) q (free_basis R s)) =
  evaluate (from_bar (bar_map_at (dual_differential F A q) f)) (free_basis R s)).
rewrite from_bar_basis bar_value_vertical /DPSimplicialChains.boundary linear_sum.
apply eq_bigr => i _; rewrite linearZ /face_map free_map_basis.
change ((-1:R)^+i *: evaluate (from_bar f)
  (free_basis R (simplex_map (fobj (replacement F) p) (coface (inord (val i))) s)) =
  (-1:R)^+i *: bar_value f (string_vertical (coface (inord (val i))) (cell_to_string s))).
rewrite from_bar_basis.
congr (_ *: _); congr (bar_value f _).
exact: cell_chart_vertical.
Qed.
End Differentials.
End DPSimplicialReplacementDualDifferentials.
