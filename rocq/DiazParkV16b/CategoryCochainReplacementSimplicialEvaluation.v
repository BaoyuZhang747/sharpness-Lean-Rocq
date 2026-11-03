(** Literal identity comparison between diagram evaluation and native Hom cochains. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalComplex HomologicalMaps CategoryComplexIso CategoryFiberVanishing.
From DiazParkV16b Require Import SimplicialSetYoneda SimplicialChains ChainDualCochain
  CategoryCochainReplacementSimplicial CategoryCochainReplacementTotal.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkHomologicalMaps DPSimplicialYoneda DPSimplicialChains
  DPChainDualCochain DPCategoryCochainReplacementSimplicial.

Module DPCategoryCochainReplacementSimplicialEvaluation.
Section Evaluation.
Variable R : comPzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable A : lmodType R.

Definition dual_evaluation_degree_iso c n : @isomorphism (module_category R)
  (cochain_term (diagram_evaluation_complex (dual_diagram F A) c) n)
  (cochain_term (@dual_complex R A (chains R (fobj F c))) n) :=
  @iso_refl (module_category R) (cochain_term (@dual_complex R A (chains R (fobj F c))) n).
Lemma dual_evaluation_differential c n x :
  cochain_d (@dual_complex R A (chains R (fobj F c))) n
    (module_hom_fun (iso_hom (dual_evaluation_degree_iso c n)) x) =
  module_hom_fun (iso_hom (dual_evaluation_degree_iso c n.+1))
    (cochain_d (diagram_evaluation_complex (dual_diagram F A) c) n x).
Proof. reflexivity. Qed.
Definition dual_evaluation_cochain c := term_iso_cochain_map (@dual_evaluation_differential c).
Definition dual_evaluation_cohomology_iso c n := term_iso_cohomology_iso (@dual_evaluation_differential c) n.

Definition dual_replacement_projection c :=
  cochain_composition (replacement_projection (dual_diagram F A) c) (dual_evaluation_cochain c).
Theorem dual_replacement_projection_formula c n
  (z : cochain_term (simplicial_cochain_replacement F A) n) :
  cochain_map_at (dual_replacement_projection c) n z = z 0%N n erefl c tt.
Proof. reflexivity. Qed.
End Evaluation.
End DPCategoryCochainReplacementSimplicialEvaluation.
