(** Literal inverse function maps between nerve cochains and the constant category bar. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules BarPaths BarComplex HomologicalComplex.
From DiazParkV16b Require Import SimplicialSet SimplicialCochains CategoryNerve
  CategoryNervePathsPrefix CategoryNervePaths CategoryBarPullbackConstant CategoryBarPullbackHomotopy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkBarComplex DiazParkHomological
  DPSimplicialSet DPSimplicialCochains DPCategoryNerve DPCategoryNervePaths
  DPCategoryNervePathEquivalence DPCategoryBarConstant DPCategoryBarHomotopy.
Local Open Scope ring_scope.

Module DPCategoryNerveCochainBarTerms.
Section Terms.
Variable R : pzRingType.
Variable C : category.
Variable A : lmodType R.
Definition nerve_bar_at n (a : cochain_functions (nerve C) A n) : cochain_term (constant_bar R C A) n :=
  fun x p => a (path_nerve (existT _ x p)).
Lemma nerve_bar_at_linear n : linear (@nerve_bar_at n).
Proof.
move=> r a b; apply functional_extensionality_dep => x;
  apply functional_extensionality_dep => p; reflexivity.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@nerve_bar_at n) (@nerve_bar_at_linear n).
Definition bar_nerve_at n (a : cochain_term (constant_bar R C A) n) : cochain_functions (nerve C) A n :=
  fun s => constant_bar_evaluate a (nerve_path s).
Lemma bar_nerve_at_linear n : linear (@bar_nerve_at n).
Proof.
move=> r a b; apply functional_extensionality_dep => s.
change (constant_bar_evaluate (r *: a+b) (nerve_path s) =
  r *: constant_bar_evaluate a (nerve_path s) + constant_bar_evaluate b (nerve_path s)).
case: (nerve_path s) => x p; reflexivity.
Qed.
HB.instance Definition _ n := GRing.isLinear.Build R _ _ _ (@bar_nerve_at n) (@bar_nerve_at_linear n).
Lemma bar_nerve_on_path n (a : cochain_term (constant_bar R C A) n) (p : @path C n) :
  bar_nerve_at a (path_nerve p) = constant_bar_evaluate a p.
Proof. by rewrite /bar_nerve_at nerve_path_nerve. Qed.
Lemma nerve_bar_evaluate n (a : cochain_functions (nerve C) A n) (p : @path C n) :
  constant_bar_evaluate (nerve_bar_at a) p = a (path_nerve p).
Proof. by case: p => x p. Qed.
Theorem nerve_bar_inverse n (a : cochain_functions (nerve C) A n) :
  bar_nerve_at (nerve_bar_at a) = a.
Proof.
apply functional_extensionality_dep => s.
by rewrite /bar_nerve_at nerve_bar_evaluate path_nerve_path.
Qed.
Theorem bar_nerve_inverse n (a : cochain_term (constant_bar R C A) n) :
  nerve_bar_at (bar_nerve_at a) = a.
Proof.
apply functional_extensionality_dep => x; apply functional_extensionality_dep => p.
change (bar_nerve_at a (path_nerve (existT _ x p)) = a x p).
by rewrite bar_nerve_on_path.
Qed.
Definition nerve_bar_degree_iso n : @isomorphism (module_category R)
  (cochain_functions (nerve C) A n) (cochain_term (constant_bar R C A) n).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear (@nerve_bar_at n)) (module_hom_of_linear (@bar_nerve_at n)) _ _).
- apply module_hom_ext => a; exact: nerve_bar_inverse.
- apply module_hom_ext => a; exact: bar_nerve_inverse.
Defined.
End Terms.
End DPCategoryNerveCochainBarTerms.
