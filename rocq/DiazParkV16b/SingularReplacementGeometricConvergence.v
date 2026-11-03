(** Finite convergence to actual singular cohomology through the actual cocone
    comparison, with its literal transported image filtration. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso.
From DiazParkV16b Require Import TopologicalCategory SingularCohomology SimplicialChainsMaps
  ChainQuasiIsomorphism SimplicialReplacementConstants SingularCochainDiagrams
  CategoryCochainReplacement SingularCochainReplacementEdge SingularCochainFilteredSecond
  FirstQuadrantCochainSpectralFiltration FilteredCochainCohomologyFiltration
  FirstQuadrantFilteredPages FirstQuadrantFilteredCohomology FirstQuadrantFilteredConvergence
  SubquotientModuleIso SingularReplacementGeometricComparison.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCohomology DPSimplicialChainMaps DPChainQuasiIsomorphism
  DPSimplicialReplacementConstants DPSingularCochainDiagrams DPSingularReplacementEdge
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalModuleIso
  DPColumnFiltration DPFilteredCohomologyFiltration DPFirstQuadrantFilteredPages
  DPFirstQuadrantFilteredCohomology DPFirstQuadrantFilteredConvergence DPSubquotientModuleIso
  DPSingularReplacementGeometricComparison.
Local Open Scope ring_scope.

Module DPSingularReplacementGeometricConvergence.
Section Convergence.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable C : category.
Variable X : functor C topological_category.
Variable Y : topologicalType.
Variable a : nat_trans X (@constant_diagram C topological_category Y).
Variable ha : quasi_isomorphism (chain_map_of R (singular_geometric_augmentation Real a)).
Let K := cochain_replacement_bicomplex (singular_cochain_diagram Real A X).
Let F := total_column_filtration K.
Let e n := @singular_geometric_cohomology_iso Real R A C X Y a ha n.

Definition singular_geometric_filtration p n :
    module_subspace [the lmodType R of singular_cohomology Real Y A n] :=
  linear_preimage (module_hom_to_linear (iso_hom (e n))) (cohomology_filtration F p n).

Theorem singular_geometric_filtration_decreasing p q n (hpq : Z.le p q) :
  subspace_le (singular_geometric_filtration q n) (singular_geometric_filtration p n).
Proof. move=> z hz; exact: (cohomology_filtration_decreasing hpq hz). Qed.
Theorem singular_geometric_filtration_zero_full n z : singular_geometric_filtration Z0 n z.
Proof. exact: total_cohomology_filtration_zero_full. Qed.
Theorem singular_geometric_filtration_bounded p n (h : (n<p)%coq_nat) z :
  singular_geometric_filtration (Z.of_nat p) n z -> z=0.
Proof.
move=> hz; apply: (module_iso_hom_injective (e := e n)).
rewrite module_hom_zero; exact: (total_cohomology_filtration_bounded h hz).
Qed.
Theorem singular_geometric_filtration_image p n z :
  singular_geometric_filtration (Z.of_nat p) n z <->
  linear_image (cohomology_map (column_inclusion K p) n)
    (cohomology_map (singular_geometric_comparison Real A a) n z).
Proof.
change (total_cohomology_filtration K p n (module_hom_fun (iso_hom (e n)) z) <->
  linear_image (cohomology_map (column_inclusion K p) n)
    (cohomology_map (singular_geometric_comparison Real A a) n z)).
rewrite total_cohomology_filtration_image singular_geometric_cohomology_iso_hom; reflexivity.
Qed.

Definition singular_geometric_associated_graded p n : lmodType R :=
  subquotient (singular_geometric_filtration p n) (singular_geometric_filtration (Z.succ p) n).
Definition singular_geometric_graded_iso p n : @isomorphism (module_category R)
    (singular_geometric_associated_graded p n) (associated_graded F p n) :=
  @subquotient_iso R _ _ (singular_geometric_filtration p n)
    (singular_geometric_filtration (Z.succ p) n) (cohomology_filtration F p n)
    (cohomology_filtration F (Z.succ p) n) (e n) (fun _ => iff_refl _) (fun _ => iff_refl _).

Definition singular_geometric_finite_convergence_iso p n : @isomorphism (module_category R)
    (singular_filtered_page Real A X (n+p+1)%coq_nat (Z.of_nat p) n)
    (singular_geometric_associated_graded (Z.of_nat p) n) :=
  module_iso_comp (total_finite_convergence_iso K p n)
    (iso_symm (singular_geometric_graded_iso (Z.of_nat p) n)).
End Convergence.
End DPSingularReplacementGeometricConvergence.
