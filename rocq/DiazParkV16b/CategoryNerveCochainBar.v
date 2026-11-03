(** Actual cochain and cohomology equivalence between the nerve and the constant category bar, over arbitrary rings. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules BarPaths BarComplex HomologicalComplex CategoryComplexIso.
From DiazParkV16b Require Import SimplicialSet SimplicialChains SimplicialCochains CategoryNerve
  CategoryNervePathsPrefix CategoryNervePaths CategoryNervePathsFaces
  CategoryBarPullbackConstant CategoryBarPullbackHomotopy CategoryNerveCochainBarTerms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkBarComplex DiazParkHomological
  DPSimplicialSet DPSimplicialCochains DPCategoryNerve DPCategoryNervePaths
  DPCategoryNervePathEquivalence DPCategoryNervePathFaces DPCategoryBarConstant
  DPCategoryBarHomotopy DPCategoryNerveCochainBarTerms.
Local Open Scope ring_scope.

Module DPCategoryNerveCochainBar.
Section Comparison.
Variable R : pzRingType.
Variable C : category.
Variable A : lmodType R.
Let N := DPSimplicialCochains.complex (nerve C) A.
Let B := constant_bar R C A.
Lemma bar_nerve_coface n (i : 'I_n.+2) (a : cochain_term B n) :
  bar_nerve_at (@bar_coface R C (constant_coefficient R C A) n i a) =
    @coface_map R (nerve C) A n i (bar_nerve_at a).
Proof.
apply functional_extensionality_dep => s.
change (constant_bar_evaluate (@bar_coface R C (constant_coefficient R C A) n i a) (nerve_path s) =
  constant_bar_evaluate a (nerve_path (@DPSimplicialChains.indexed_face (nerve C) n i s))).
rewrite constant_bar_evaluate_coface /DPSimplicialChains.indexed_face nerve_path_face.
have hi : val (inord (val i) : 'I_n.+2) = val i by apply: inordK; exact: ltn_ord.
by rewrite hi.
Qed.
Theorem bar_nerve_d n (a : cochain_term B n) :
  cochain_d N n (bar_nerve_at a) = bar_nerve_at (cochain_d B n a).
Proof.
change (\sum_(i < n.+2) (-1:R)^+i *: @coface_map R (nerve C) A n i (bar_nerve_at a) =
  bar_nerve_at (\sum_(i < n.+2) (-1:R)^+i *: @bar_coface R C (constant_coefficient R C A) n i a)).
rewrite linear_sum; apply eq_bigr => i _.
rewrite linearZ; congr (_ *: _); symmetry; exact: bar_nerve_coface.
Qed.
Theorem nerve_bar_d n (a : cochain_term N n) :
  cochain_d B n (nerve_bar_at a) = nerve_bar_at (cochain_d N n a).
Proof.
apply (can_inj (@bar_nerve_inverse R C A n.+1)).
by rewrite -bar_nerve_d !nerve_bar_inverse.
Qed.
Definition nerve_bar_cochain_map : cochain_map N B :=
  @term_iso_cochain_map R N B (@nerve_bar_degree_iso R C A) nerve_bar_d.
Definition bar_nerve_cochain_map : cochain_map B N :=
  @term_iso_cochain_inverse R N B (@nerve_bar_degree_iso R C A) nerve_bar_d.
Definition nerve_bar_cohomology_iso n :=
  @term_iso_cohomology_iso R N B (@nerve_bar_degree_iso R C A) nerve_bar_d n.
Theorem nerve_bar_cochain_formula n a x p :
  cochain_map_at nerve_bar_cochain_map n a x p = a (path_nerve (existT _ x p)).
Proof. reflexivity. Qed.
Theorem bar_nerve_cochain_formula n a s :
  cochain_map_at bar_nerve_cochain_map n a s = constant_bar_evaluate a (nerve_path s).
Proof. reflexivity. Qed.
Theorem nerve_bar_cochain_left n a :
  cochain_map_at bar_nerve_cochain_map n (cochain_map_at nerve_bar_cochain_map n a) = a.
Proof. exact: nerve_bar_inverse. Qed.
Theorem nerve_bar_cochain_right n a :
  cochain_map_at nerve_bar_cochain_map n (cochain_map_at bar_nerve_cochain_map n a) = a.
Proof. exact: bar_nerve_inverse. Qed.
End Comparison.
End DPCategoryNerveCochainBar.
