(** Actual arbitrary-coefficient augmentation comparison and literal restriction maps. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear HomologicalComplex HomologicalMaps
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso BarFreeModule.
From DiazParkV16b Require Import ChainComplex LinearMapSpace LinearProjective ChainDualCochain
  ChainDualProjectiveQuasiIso ChainQuasiIsomorphism CochainMapsLaws SimplicialSet SimplicialSetYoneda
  SimplicialChains SimplicialChainsMaps BisimplicialSet BisimplicialChains FirstQuadrantChainTotalProjective
  SimplicialReplacementConstants SimplicialReplacement SimplicialReplacementAugmentation
  CategoryCochainReplacementSimplicial CategoryCochainReplacementSimplicialEvaluation CategoryCochainReplacementTotal
  SimplicialReplacementDualTotal SimplicialReplacementCoconeTotal.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalModuleIso DPChainComplex DPLinearMapSpace DPLinearProjective
  DPChainDualCochain DPChainDualProjectiveQuasiIso DPChainQuasiIsomorphism DPCochainMapsLaws
  DPSimplicialSet DPSimplicialYoneda DPSimplicialChains DPSimplicialChainMaps DPBisimplicialSet DPBisimplicialChains
  DPFirstQuadrantChainTotalProjective DPSimplicialReplacementConstants DPSimplicialReplacement
  DPSimplicialReplacementAugmentation DPCategoryCochainReplacementSimplicial
  DPSimplicialReplacementDualTotal DPSimplicialReplacementCoconeTotal
  DPCategoryCochainReplacementSimplicialEvaluation.
Local Open Scope ring_scope.

Module DPSimplicialReplacementCoconeDual.
Section Projectivity.
Variable R : pzRingType.
Variable X : bisimplicial_set.
Theorem bisimplicial_total_projective n : linear_projective (chain_term (total_chains R X) n).
Proof. apply total_term_projective => p q; exact: free_projective. Qed.
End Projectivity.

Section Comparison.
Variable R : comPzRingType.
Variable C : category.
Variable F : functor C simplicial_category.
Variable X : simplicial_set.
Variable a : nat_trans F (@constant_diagram C simplicial_category X).
Variable A : lmodType R.
Let E := @dual_complex R A (chains R X).
Let B := simplicial_cochain_replacement F A.
Let f := cocone_total_augmentation R a.

Definition cocone_dual_comparison : cochain_map E B :=
  cochain_composition (dual_map A f) (replacement_dual_cochain F A).

Theorem cocone_dual_restriction n (z : cochain_term E n) c :
  cochain_map_at (replacement_projection (dual_diagram F A) c) n
    (cochain_map_at cocone_dual_comparison n z) =
  cochain_map_at (dual_map A (chain_map_of R (component a c))) n z.
Proof.
apply ext => x.
change (evaluate (cochain_map_at (replacement_projection (dual_diagram F A) c) n
  (cochain_map_at (replacement_dual_cochain F A) n (cochain_map_at (dual_map A f) n z))) x =
  evaluate z (map_at R (component a c) n x)).
rewrite replacement_dual_projection dual_map_evaluate.
change (evaluate z (chain_map_at (cocone_total_augmentation R a) n
  (@FirstQuadrantChainTotalSupport.DPFirstQuadrantChainSupport.total_include R
    (bisimplicial_bicomplex R (replacement F)) 0 n n erefl
    (free_map R (@zero_cell C F c n) x))) = evaluate z (map_at R (component a c) n x)).
by rewrite cocone_total_augmentation_include.
Qed.

Theorem cocone_dual_cohomology_restriction n (z : cohomology E n) c :
  cohomology_map (dual_replacement_projection F A c) n
    (cohomology_map cocone_dual_comparison n z) =
  cohomology_map (dual_map A (chain_map_of R (component a c))) n z.
Proof.
symmetry; apply cohomology_composition_of => x; symmetry; exact: cocone_dual_restriction.
Qed.

Variable ha : quasi_isomorphism f.
Definition cocone_dual_cohomology_iso n :=
  module_iso_comp
    (@dual_projective_cohomology_iso R A (total_chains R (replacement F)) (chains R X) f
      (@bisimplicial_total_projective R (replacement F)) (fun k => @free_projective R (simplex X k))
      ha n)
    (replacement_dual_cohomology_iso F A n).

Theorem cocone_dual_cohomology_iso_hom n (z : cohomology E n) :
  module_hom_fun (iso_hom (cocone_dual_cohomology_iso n)) z =
  cohomology_map cocone_dual_comparison n z.
Proof. symmetry; exact: cohomology_map_composition. Qed.

Theorem cocone_dual_cohomology_iso_restriction n (z : cohomology E n) c :
  cohomology_map (dual_replacement_projection F A c) n
    (module_hom_fun (iso_hom (cocone_dual_cohomology_iso n)) z) =
  cohomology_map (dual_map A (chain_map_of R (component a c))) n z.
Proof. by rewrite cocone_dual_cohomology_iso_hom cocone_dual_cohomology_restriction. Qed.
End Comparison.
End DPSimplicialReplacementCoconeDual.
