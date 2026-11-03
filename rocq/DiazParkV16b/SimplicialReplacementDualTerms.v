(** Literal Hom on replacement chains equals the category-bar term of objectwise Hom. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules BarPaths BarComplex BarFreeModule.
From DiazParkV16b Require Import SimplicialSet SimplicialSetYoneda BisimplicialChains SimplicialReplacement
  SimplicialReplacementTypes SimplicialReplacementDualCells CategoryCochainReplacementSimplicial
  LinearMapSpace FreeLinearMapSpace.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkBarComplex DiazParkFreeModule DPSimplicialSet
  DPSimplicialYoneda DPBisimplicialChains DPSimplicialReplacement DPSimplicialReplacementTypes
  DPSimplicialReplacementDualCells DPCategoryCochainReplacementSimplicial DPLinearMapSpace DPFreeLinearMapSpace.
Local Open Scope ring_scope.

Module DPSimplicialReplacementDualTerms.
Section Terms.
Variable R : comPzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable A : lmodType R.
Variables p q : nat.
Definition cell_hom : lmodType R := linear_maps (bi_term R (replacement F) p q) A.
Definition bar_hom : lmodType R := bar_term (dual_degree F A q) p.

Definition to_bar (f : cell_hom) : bar_hom := fun c t =>
  of_linear (free_lift (fun x : simplex (fobj F c) q =>
    evaluate f (free_basis R (string_to_cell (existT _ c (t,x))))) : {linear _ -> A}).
Arguments to_bar _ _ _ : clear implicits.
Lemma to_bar_basis (f : cell_hom) c t x :
  evaluate (to_bar f c t) (free_basis R x) =
    evaluate f (free_basis R (string_to_cell (existT _ c (t,x)))).
Proof. exact: free_lift_basis. Qed.
Lemma to_bar_linear : linear to_bar.
Proof.
move=> r f g; apply functional_extensionality_dep => c; apply functional_extensionality_dep => t.
apply ext => x; apply (free_lift_ext (g := as_linear (to_bar (r *: f+g) c t))
  (h := as_linear (r *: to_bar f c t+to_bar g c t))) => y.
change (evaluate (to_bar (r *: f+g) c t) (free_basis R y) =
  r *: evaluate (to_bar f c t) (free_basis R y)+evaluate (to_bar g c t) (free_basis R y)).
by rewrite !to_bar_basis.
Qed.
Definition to_bar_hom : module_hom cell_hom bar_hom.
Proof. exists to_bar; exact to_bar_linear. Defined.

Definition bar_value (f : bar_hom) (a : string_cell F p q) : A :=
  match a with existT c (t,x) => evaluate (f c t) (free_basis R x) end.
Definition from_bar (f : bar_hom) : cell_hom :=
  of_linear (free_lift (fun a : replacement_cell F p q => bar_value f (cell_to_string a)) : {linear _ -> A}).
Lemma from_bar_basis (f : bar_hom) a :
  evaluate (from_bar f) (free_basis R a) = bar_value f (cell_to_string a).
Proof. exact: free_lift_basis. Qed.
Lemma bar_value_linear r (f g : bar_hom) a :
  bar_value (r *: f+g) a = r *: bar_value f a+bar_value g a.
Proof. by case: a => c [t x]. Qed.
Lemma from_bar_linear : linear from_bar.
Proof.
move=> r f g; apply ext => x; apply (free_lift_ext (g := as_linear (from_bar (r *: f+g)))
  (h := as_linear (r *: from_bar f+from_bar g))) => a.
change (evaluate (from_bar (r *: f+g)) (free_basis R a) =
  r *: evaluate (from_bar f) (free_basis R a)+evaluate (from_bar g) (free_basis R a)).
by rewrite !from_bar_basis bar_value_linear.
Qed.
Definition from_bar_hom : module_hom bar_hom cell_hom.
Proof. exists from_bar; exact from_bar_linear. Defined.

Lemma to_bar_value (f : cell_hom) a :
  bar_value (to_bar f) a = evaluate f (free_basis R (string_to_cell a)).
Proof. case: a => c [t x]; exact: to_bar_basis. Qed.
Lemma from_to_bar (f : cell_hom) : from_bar (to_bar f)=f.
Proof.
apply ext => x; apply (free_lift_ext (g := as_linear (from_bar (to_bar f))) (h := as_linear f)) => a.
by rewrite /= from_bar_basis to_bar_value string_cell_inverse.
Qed.
Lemma to_from_bar (f : bar_hom) : to_bar (from_bar f)=f.
Proof.
apply functional_extensionality_dep => c; apply functional_extensionality_dep => t.
apply ext => x; apply (free_lift_ext (g := as_linear (to_bar (from_bar f) c t)) (h := as_linear (f c t))) => y.
by rewrite /= to_bar_basis from_bar_basis cell_string_inverse.
Qed.

Definition cell_bar_hom_iso : @isomorphism (module_category R) cell_hom bar_hom.
Proof.
refine (@Build_isomorphism (module_category R) cell_hom bar_hom
  to_bar_hom from_bar_hom _ _).
- apply module_hom_ext => f; exact: from_to_bar.
- apply module_hom_ext => f; exact: to_from_bar.
Defined.
End Terms.
End DPSimplicialReplacementDualTerms.
