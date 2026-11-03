(** The actual singular cocone induces the geometric cohomology comparison,
    with literal restrictions. Only its actual diagonal chain quasi-isomorphism
    is the comparison criterion. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear CategoryModuleExactness
  CategoryComplexIso HomologicalComplex HomologicalMaps HomologicalCohomology HomologicalCohomologyMaps
  HomologicalModuleIso MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import TopologicalCategory SingularSet SingularCohomology
  SimplicialSet SimplicialSetYoneda SimplicialChains SimplicialChainsMaps SimplicialCochains
  SimplicialCochainQuasiIso ChainDualCochain ChainQuasiIsomorphism CochainMapsLaws
  GeometricRealizationSingularAdjunction SimplicialReplacementConstants SimplicialReplacementAugmentation
  SimplicialReplacementCoconeDual SimplicialReplacementCoconeQuasiIso
  CategoryCochainReplacementSimplicialEvaluation SingularCochainReplacementEdge SingularCochainReplacementDual.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DPTopological DPSingularSet DPSingularCohomology DPSimplicialSet
  DPSimplicialYoneda DPSimplicialChains DPSimplicialChainMaps DPSimplicialCochains
  DPSimplicialCochainQuasiIso DPChainDualCochain DPChainQuasiIsomorphism DPCochainMapsLaws
  DPGeometricRealizationSingularAdjunction DPSimplicialReplacementConstants
  DPSimplicialReplacementAugmentation DPSimplicialReplacementCoconeDual
  DPSimplicialReplacementCoconeQuasiIso DPCategoryCochainReplacementSimplicialEvaluation
  DPSingularReplacementEdge DPSingularCochainReplacementDual.

Module DPSingularReplacementGeometricComparison.
Section Cocone.
Variable Real : realType.
Variable C : category.
Variable X : functor C topological_category.
Variable Y : topologicalType.
Variable a : nat_trans X (@constant_diagram C topological_category Y).
Definition singular_topological_cocone :
    nat_trans (functor_comp X (singular_functor Real))
      (@constant_diagram C simplicial_category (singular_set Real Y)).
Proof.
refine (@Build_nat_trans C simplicial_category (functor_comp X (singular_functor Real))
  (@constant_diagram C simplicial_category (singular_set Real Y))
  (fun c => singular_map Real (component a c)) _).
move=> c d f.
change (@compose simplicial_category _ _ _
  (fmap (singular_functor Real) (fmap X f)) (fmap (singular_functor Real) (component a d)) =
  @compose simplicial_category _ _ _ (fmap (singular_functor Real) (component a c))
    (@identity simplicial_category (singular_set Real Y))).
rewrite -fmap_compose compose_id_right.
have e : @compose topological_category _ _ _ (fmap X f) (component a d) = component a c.
  have h := naturality a f; rewrite compose_id_right in h; exact h.
by rewrite e.
Defined.
Definition singular_geometric_augmentation := diagonal_coefficient_augmentation singular_topological_cocone.
Lemma singular_topological_cocone_component c :
  component singular_topological_cocone c = singular_map Real (component a c).
Proof. reflexivity. Qed.
End Cocone.

Section Comparison.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable C : category.
Variable X : functor C topological_category.
Variable Y : topologicalType.
Variable a : nat_trans X (@constant_diagram C topological_category Y).
Let F := functor_comp X (singular_functor Real).
Let b := singular_topological_cocone Real a.
Let T := singular_replacement_total Real A X.

Definition singular_functions_dual : cochain_map (singular_cochains Real Y A)
    (@dual_complex R A (chains R (singular_set Real Y))) :=
  @term_iso_cochain_inverse R _ _ (@dual_function_iso R (singular_set Real Y) A)
    (@dual_function_differential R (singular_set Real Y) A).
Definition singular_geometric_comparison : cochain_map (singular_cochains Real Y A) T :=
  cochain_composition singular_functions_dual
    (cochain_composition (cocone_dual_comparison b A) (singular_dual_total_cochain Real A X)).

Theorem singular_geometric_comparison_restriction k z c :
  cochain_map_at (singular_replacement_projection Real A X c) k
    (cochain_map_at singular_geometric_comparison k z) =
  cochain_map_at (singular_pullback Real (component a c) A) k z.
Proof.
change (cochain_map_at (singular_replacement_projection Real A X c) k
  (cochain_map_at (singular_dual_total_cochain Real A X) k
    (cochain_map_at (cocone_dual_comparison b A) k (cochain_map_at singular_functions_dual k z))) =
  cochain_map_at (singular_pullback Real (component a c) A) k z).
rewrite singular_dual_total_projection cocone_dual_restriction dual_functions_pull_square.
change (cochain_map_at (singular_pullback Real (component a c) A) k
  (module_hom_fun (iso_hom (dual_function_iso (singular_set Real Y) A k))
    (module_hom_fun (iso_inv (dual_function_iso (singular_set Real Y) A k)) z)) =
  cochain_map_at (singular_pullback Real (component a c) A) k z).
by rewrite module_iso_inv_hom_apply.
Qed.
Theorem singular_geometric_cohomology_restriction k z c :
  cohomology_map (singular_replacement_projection Real A X c) k
    (cohomology_map singular_geometric_comparison k z) =
  singular_cohomology_map Real (component a c) A k z.
Proof.
symmetry; apply cohomology_composition_of => w; symmetry; exact: singular_geometric_comparison_restriction.
Qed.

Variable ha : quasi_isomorphism (chain_map_of R (singular_geometric_augmentation Real a)).
Definition singular_geometric_cohomology_iso k : @isomorphism (module_category R)
    [the lmodType R of singular_cohomology Real Y A k] (cohomology T k) :=
  module_iso_comp (iso_symm (dual_function_cohomology_iso (singular_set Real Y) A k))
    (module_iso_comp (@cocone_dual_iso_of_diagonal R C F (singular_set Real Y) b A ha k)
      (singular_dual_total_cohomology_iso Real A X k)).
Theorem singular_geometric_cohomology_iso_hom k z :
  module_hom_fun (iso_hom (singular_geometric_cohomology_iso k)) z =
    cohomology_map singular_geometric_comparison k z.
Proof.
change (module_hom_fun (iso_hom (singular_dual_total_cohomology_iso Real A X k))
  (module_hom_fun (iso_hom (@cocone_dual_iso_of_diagonal R C F (singular_set Real Y) b A ha k))
    (module_hom_fun (iso_inv (dual_function_cohomology_iso (singular_set Real Y) A k)) z)) =
  cohomology_map singular_geometric_comparison k z).
rewrite singular_dual_total_cohomology_iso_hom cocone_dual_iso_of_diagonal_hom.
symmetry.
refine (eq_trans (@cohomology_map_composition R _ _ _ singular_functions_dual
  (cochain_composition (cocone_dual_comparison b A) (singular_dual_total_cochain Real A X)) k z) _).
exact (@cohomology_map_composition R _ _ _ (cocone_dual_comparison b A)
  (singular_dual_total_cochain Real A X) k (cohomology_map singular_functions_dual k z)).
Qed.
Theorem singular_geometric_cohomology_iso_restriction k z c :
  cohomology_map (singular_replacement_projection Real A X c) k
    (module_hom_fun (iso_hom (singular_geometric_cohomology_iso k)) z) =
  singular_cohomology_map Real (component a c) A k z.
Proof. by rewrite singular_geometric_cohomology_iso_hom singular_geometric_cohomology_restriction. Qed.
End Comparison.
End DPSingularReplacementGeometricComparison.
