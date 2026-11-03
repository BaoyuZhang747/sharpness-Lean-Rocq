(** The actual geometric spectral edge, with every component the literal
    singular-cohomology restriction along the topological cocone. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso MackeyModuleQuotient.
From DiazParkV16b Require Import TopologicalCategory SingularCohomology SimplicialChainsMaps
  ChainQuasiIsomorphism SimplicialReplacementConstants SingularCochainReplacementEdge
  SingularCochainFilteredCollapse SingularCochainFilteredEdgeComparison SingularReplacementGeometricComparison.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCohomology DPSimplicialChainMaps DPChainQuasiIsomorphism
  DPSimplicialReplacementConstants DPSingularReplacementEdge DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalModuleIso DPSingularReplacementGeometricComparison.

Module DPSingularReplacementGeometricEdge.
Section Edge.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable C : category.
Variable X : functor C topological_category.
Variable Y : topologicalType.
Variable a : nat_trans X (@constant_diagram C topological_category Y).
Variable ha : quasi_isomorphism (chain_map_of R (singular_geometric_augmentation Real a)).
Variable hX : singular_positive_limits_vanish Real A X.

Definition singular_geometric_limit_iso n : @isomorphism (module_category R)
    [the lmodType R of singular_cohomology Real Y A n]
    (module_limit_type (singular_cohomology_diagram Real A X n)) :=
  module_iso_comp (@singular_geometric_cohomology_iso Real R A C X Y a ha n)
    (singular_filtered_total_limit_iso hX n).

Theorem singular_geometric_limit_iso_component n z c :
  module_limit_val (module_hom_fun (iso_hom (singular_geometric_limit_iso n)) z) c =
    singular_cohomology_map Real (component a c) A n z.
Proof.
change (module_limit_val (module_hom_fun (iso_hom (singular_filtered_total_limit_iso hX n))
  (module_hom_fun (iso_hom (@singular_geometric_cohomology_iso Real R A C X Y a ha n)) z)) c =
  singular_cohomology_map Real (component a c) A n z).
rewrite singular_filtered_total_limit_iso_component.
exact (@singular_geometric_cohomology_iso_restriction Real R A C X Y a ha n z c).
Qed.

Theorem singular_geometric_limit_iso_is_spectral_edge n z :
  module_hom_fun (iso_hom (singular_geometric_limit_iso n)) z =
    module_hom_fun (iso_hom (singular_filtered_total_limit_iso hX n))
      (cohomology_map (singular_geometric_comparison Real A a) n z).
Proof.
change (module_hom_fun (iso_hom (singular_filtered_total_limit_iso hX n))
  (module_hom_fun (iso_hom (@singular_geometric_cohomology_iso Real R A C X Y a ha n)) z) =
  module_hom_fun (iso_hom (singular_filtered_total_limit_iso hX n))
    (cohomology_map (singular_geometric_comparison Real A a) n z)).
by rewrite singular_geometric_cohomology_iso_hom.
Qed.
End Edge.
End DPSingularReplacementGeometricEdge.
