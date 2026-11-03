(** Literal forgetful compatibility at the distinguished group-category
    coordinate. This supplies the map identity used in the final E3 square. *)
From mathcomp Require Import all_boot all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryModules FusionSystems.
From DiazParkV16b Require Import LinkingSystem LinkingCommaCategory CategoryNerve
  CategoryConstantCohomology SingularCohomology GeometricRealizationCarrier
  GeometricRealizationMaps RealizationNerveCohomologyUnconditional GroupClassifyingCohomology.
From DiazParkBLO Require Import BLODiagram BLOCohomologyDistinguished.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCategoryNerve DPSingularCohomology DPGeometricRealization
  DPGeometricRealizationMaps DPRealizationNerveCohomologyUnconditional
  DPGroupClassifyingCohomology DPBLODiagram DPBLOCohomologyDistinguished.

Module DPBLOEdgeCoordinates.
Section Coordinate.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable E : {group S}.
Variable R : comPzRingType.
Variable A : lmodType R.

Theorem distinguished_forgetful_square (X : enlarged_object F E) n z :
  module_hom_fun (DPCategoryConstantCohomology.pull A
    (DPBLOCohomologyDistinguished.distinguished_functor L X) n)
    (module_hom_fun (iso_hom (comparison_iso_unconditional Real A
      (enlarged_category L E) n))
      (singular_cohomology_map Real
        (realization_map Real (nerve_map (forgetful L E))) A n z)) =
  module_hom_fun (iso_hom (group_comparison_iso Real A
    [the finGroupType of ([subg (val (underlying X))]%type)] n))
    (singular_cohomology_map Real
      (realization_map Real (nerve_map
        (DPLinkingComma.distinguished_functor L (underlying X)))) A n z).
Proof.
rewrite comparison_iso_unconditional_natural.
change (module_hom_fun (module_hom_comp
  (DPCategoryConstantCohomology.pull A (forgetful L E) n)
  (DPCategoryConstantCohomology.pull A
    (DPBLOCohomologyDistinguished.distinguished_functor L X) n))
  (module_hom_fun (iso_hom (comparison_iso_unconditional Real A
    (DPCentricLinking.linking_category L) n)) z) =
  module_hom_fun (iso_hom (group_comparison_iso Real A
    [the finGroupType of ([subg (val (underlying X))]%type)] n))
    (singular_cohomology_map Real
      (realization_map Real (nerve_map
        (DPLinkingComma.distinguished_functor L (underlying X)))) A n z)).
rewrite -DPCategoryConstantCohomology.pull_composition distinguished_forgetful.
symmetry; exact: comparison_iso_unconditional_natural.
Qed.
End Coordinate.
End DPBLOEdgeCoordinates.
