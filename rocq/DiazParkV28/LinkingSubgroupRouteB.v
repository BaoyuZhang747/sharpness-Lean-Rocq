(** Subgroup sharpness and its literal native edge, from the new Route B chain. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits CategoryModuleExactness
 CategoryDerivedLimits HomologicalCohomologyMaps HomologicalModuleIso FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingOrbitProjection LinkingCommaCategory
 LinkingCommaCohomology LinkingCommaCohomologyNatIso GroupCohomologyOrbitCoefficient
 SimplicialSet CategoryNerve SingularCohomology RealizationUnitComparison
 RealizationNerveCohomology GroupClassifyingCohomology LinkingSubgroupRealizationComparison
 CategoryRealizationDecomposition CategoryRealizationCohomologyDiagram ModuleLimitIsoComponents
 SingularCochainReplacementEdge GeometricRealizationCarrier GeometricRealizationMaps
 CategoryConstantCohomology.
From DiazParkV28 Require Import GroupCohomologyRouteB.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DiazParkCohomologyMaps DPSimplicialSet
 DPCategoryNerve DPSingularCohomology DPGeometricRealization DPGeometricRealizationMaps
 DPRealizationUnitComparison DPRealizationNerveCohomology DPGroupClassifyingCohomology
 DPLinkingSubgroupRealizationComparison DPSingularReplacementEdge
 DPCategoryRealizationCohomologyDiagram.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV28LinkingSubgroup.
Section Subgroup.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable K : fieldType.
Variable charp : p \in [pchar K].
Variable A : lmodType K.
Local Notation R := [the comPzRingType of (K : Type)].
Local Notation hunit := (fun X => realization_unit_quasi_isomorphism Real R X).
Local Notation O := (DPFusionOrbit.centric_orbit_category F).
Local Notation Y := (realization_space Real (nerve (DPCentricLinking.linking_category L))).

Theorem field_positive_limits :
  singular_positive_limits_vanish Real A (subgroup_space_diagram Real L).
Proof.
move=> n j x.
pose e := @subgroup_native_higher_limit_iso Real S F L R hunit A n j.+1.
apply (module_iso_hom_injective (e := e)); rewrite module_hom_zero.
exact (@DPV28GroupCohomologySharpness.field_higher_limits_zero S F p hS sat K charp A n j
  (module_hom_fun (iso_hom e) x)).
Qed.

Definition field_edge_iso n :=
  @DPCategoryRealizationDecomposition.limit_iso Real _ _
    (DPLinkingOrbit.orbit_projection L) R A field_positive_limits n.

Theorem field_edge_component n z P :
  module_limit_val (module_hom_fun (iso_hom (field_edge_iso n)) z) P =
  singular_cohomology_map Real
    (component (DPCategoryRealizationDecomposition.space_cocone Real
      (DPLinkingOrbit.orbit_projection L)) P) A n z.
Proof. exact: DPCategoryRealizationDecomposition.limit_iso_component. Qed.

Definition native_coefficient_iso n :=
  diagram_iso_comp (@subgroup_comma_cohomology_nat_iso Real S F L R hunit A n)
    (@DPLinkingCommaCohomologyNatIso.comparison_nat_iso R A S F L n).

Definition native_limit_iso n :=
  @DPModuleLimitIsoComponents.limit_iso R (opposite O) _ _ (native_coefficient_iso n).

Definition native_edge_iso n :=
  module_iso_comp (field_edge_iso n) (native_limit_iso n).

Theorem native_edge_component n z P :
  module_limit_val (module_hom_fun (iso_hom (native_edge_iso n)) z) P =
  module_hom_fun (iso_hom (group_comparison_iso Real A [the finGroupType of ([subg (val P)]%type)] n))
    (singular_cohomology_map Real
      (realization_map Real (nerve_map (DPLinkingComma.distinguished_functor L P))) A n z).
Proof.
set rhs := (module_hom_fun (iso_hom
  (group_comparison_iso Real A [the finGroupType of ([subg (val P)]%type)] n))
  (singular_cohomology_map Real
    (realization_map Real (nerve_map (DPLinkingComma.distinguished_functor L P))) A n z)).
change (module_limit_val (module_hom_fun (iso_hom (native_limit_iso n))
  (module_hom_fun (iso_hom (field_edge_iso n)) z)) P = rhs).
rewrite DPModuleLimitIsoComponents.limit_iso_component field_edge_component.
change (module_hom_fun (iso_hom (DPLinkingCommaCohomology.comparison_iso A L P n))
  (module_hom_fun (iso_hom (@subgroup_comma_cohomology_iso Real S F L R hunit A n P))
    (singular_cohomology_map Real
      (realization_map Real (nerve_map (DPLinkingComma.subgroup_comma_forget L P))) A n z)) = rhs).
rewrite /subgroup_comma_cohomology_iso comparison_iso_forward comparison_cohomology_natural.
change (module_hom_fun (module_hom_comp
  (DPCategoryConstantCohomology.pull A (DPLinkingComma.subgroup_comma_forget L P) n)
  (iso_hom (DPLinkingCommaCohomology.comparison_iso A L P n)))
  (cohomology_map (comparison_cochain Real A (DPCentricLinking.linking_category L)) n z) = rhs).
rewrite /rhs DPLinkingCommaCohomology.comparison_forget group_comparison_iso_forward.
symmetry; exact: comparison_cohomology_natural.
Qed.
End Subgroup.
End DPV28LinkingSubgroup.
