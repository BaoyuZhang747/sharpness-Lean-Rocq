(** Actual total cochain isomorphism, including the literal restriction edge. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness HomologicalComplex
  HomologicalModuleIso CategoryComplexIso BarPaths BarFreeModule.
From DiazParkV16b Require Import SimplicialSet SimplicialSetYoneda SimplicialChains CategoryNervePaths
  BisimplicialChains SimplicialReplacement SimplicialReplacementTypes ChainDualCochain LinearMapSpace
  ChainTotalDual ChainTotalDualCochain FirstQuadrantChainTotalSupport
  FirstQuadrantCochainTotal FirstQuadrantCochainTotalMaps CategoryCochainReplacement CategoryCochainReplacementTotal
  CategoryCochainReplacementSimplicial SimplicialReplacementDualCells SimplicialReplacementDualTerms
  SimplicialReplacementDualBicomplex.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalModuleIso DiazParkBarPaths
  DiazParkFreeModule DPSimplicialSet DPSimplicialYoneda DPSimplicialChains DPCategoryNervePathEquivalence
  DPBisimplicialChains DPSimplicialReplacement DPSimplicialReplacementTypes DPChainDualCochain DPLinearMapSpace
  DPChainTotalDual DPChainTotalDualCochain DPFirstQuadrantChainSupport DPFirstQuadrantTotalMaps
  DPCategoryCochainReplacementSimplicial DPSimplicialReplacementDualCells DPSimplicialReplacementDualTerms
  DPSimplicialReplacementDualBicomplex.
Local Open Scope ring_scope.

Module DPSimplicialReplacementDualTotal.
Section Comparison.
Variable R : comPzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable A : lmodType R.
Let K := bisimplicial_bicomplex R (replacement F).
Let D := @dual_complex R A (total_chains R (replacement F)).
Let T := DPFirstQuadrantTotal.total_complex (dual_bicomplex A K).
Let B := simplicial_cochain_replacement F A.

Definition total_bar_forward : cochain_map T B := total_cochain_map (to_bar_bicomplex F A).
Definition total_bar_inverse : cochain_map B T := total_cochain_map (from_bar_bicomplex F A).

Definition total_bar_degree_iso n : @isomorphism (module_category R) (cochain_term T n) (cochain_term B n).
Proof.
refine (@Build_isomorphism (module_category R) (cochain_term T n) (cochain_term B n)
  (module_hom_of_linear (cochain_map_at total_bar_forward n))
  (module_hom_of_linear (cochain_map_at total_bar_inverse n)) _ _).
- apply module_hom_ext => a; apply functional_extensionality_dep => p.
  apply functional_extensionality_dep => q; apply functional_extensionality_dep => h.
  exact: bicomplex_comparison_left.
- apply module_hom_ext => a; apply functional_extensionality_dep => p.
  apply functional_extensionality_dep => q; apply functional_extensionality_dep => h.
  exact: bicomplex_comparison_right.
Defined.

Definition replacement_dual_degree_iso n :=
  module_iso_comp (total_dual_degree_iso A K n) (total_bar_degree_iso n).

Lemma replacement_dual_differential n (f : cochain_term D n) :
  cochain_d B n (module_hom_fun (iso_hom (replacement_dual_degree_iso n)) f) =
  module_hom_fun (iso_hom (replacement_dual_degree_iso n.+1)) (cochain_d D n f).
Proof.
change (cochain_d B n (cochain_map_at total_bar_forward n
  (cochain_map_at (total_dual_cochain_map A K) n f)) =
  cochain_map_at total_bar_forward n.+1
  (cochain_map_at (total_dual_cochain_map A K) n.+1 (cochain_d D n f))).
by rewrite !cochain_map_commutes.
Qed.

Definition replacement_dual_cochain : cochain_map D B :=
  @term_iso_cochain_map R D B replacement_dual_degree_iso replacement_dual_differential.
Definition replacement_dual_cochain_inverse : cochain_map B D :=
  @term_iso_cochain_inverse R D B replacement_dual_degree_iso replacement_dual_differential.
Definition replacement_dual_cohomology_iso n :=
  @term_iso_cohomology_iso R D B replacement_dual_degree_iso replacement_dual_differential n.

Theorem replacement_dual_cochain_left n f :
  cochain_map_at replacement_dual_cochain_inverse n (cochain_map_at replacement_dual_cochain n f)=f.
Proof. exact: module_iso_hom_inv_apply. Qed.
Theorem replacement_dual_cochain_right n a :
  cochain_map_at replacement_dual_cochain n (cochain_map_at replacement_dual_cochain_inverse n a)=a.
Proof. exact: module_iso_inv_hom_apply. Qed.

Theorem replacement_dual_component n f p q (h : (p+q)%coq_nat=n) c t x :
  evaluate (cochain_map_at replacement_dual_cochain n f p q h c t) (free_basis R x) =
  evaluate f (@total_include R K p q n h
    (free_basis R (string_to_cell (existT _ c (t,x))))).
Proof.
change (evaluate (@to_bar R C F A p q (@total_dual_forward R A K n f p q h) c t)
  (free_basis R x) = evaluate f (@total_include R K p q n h
    (free_basis R (string_to_cell (existT _ c (t,x)))))).
rewrite to_bar_basis; reflexivity.
Qed.

Definition zero_cell c n (x : simplex (fobj F c) n) : replacement_cell F 0 n :=
  existT _ (constant_nerve c 0) x.
Lemma zero_cell_inverse c n (x : simplex (fobj F c) n) :
  @string_to_cell C F 0 n (existT _ c (tt,x)) = zero_cell x.
Proof. apply cell_to_string_injective; rewrite cell_string_inverse; reflexivity. Qed.

Theorem replacement_dual_projection_basis n f c (x : simplex (fobj F c) n) :
  evaluate (cochain_map_at (replacement_projection (dual_diagram F A) c) n
    (cochain_map_at replacement_dual_cochain n f)) (free_basis R x) =
  evaluate f (@total_include R K 0 n n erefl (free_basis R (zero_cell x))).
Proof. by rewrite replacement_projection_formula replacement_dual_component zero_cell_inverse. Qed.

Theorem replacement_dual_projection n f c (x : term R (fobj F c) n) :
  evaluate (cochain_map_at (replacement_projection (dual_diagram F A) c) n
    (cochain_map_at replacement_dual_cochain n f)) x =
  evaluate f (@total_include R K 0 n n erefl (free_map R (@zero_cell c n) x)).
Proof.
apply (free_lift_ext
  (g := as_linear (cochain_map_at (replacement_projection (dual_diagram F A) c) n
    (cochain_map_at replacement_dual_cochain n f)))
  (h := (as_linear f \o @total_include R K 0 n n erefl \o free_map R (@zero_cell c n) : {linear _ -> _}))) => y.
change (evaluate (cochain_map_at (replacement_projection (dual_diagram F A) c) n
  (cochain_map_at replacement_dual_cochain n f)) (free_basis R y) =
  evaluate f (@total_include R K 0 n n erefl (free_map R (@zero_cell c n) (free_basis R y)))).
by rewrite free_map_basis replacement_dual_projection_basis.
Qed.
End Comparison.
End DPSimplicialReplacementDualTotal.
