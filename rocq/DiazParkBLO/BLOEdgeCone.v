(** The literal compatible family of forgetful pullbacks. Its construction
    requires neither higher-limit vanishing nor a comparison isomorphism. *)
From mathcomp Require Import all_boot all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryLimits CategoryModules CategoryModuleLimits
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  MackeyModuleCarriers MackeyModuleQuotient FusionSystems FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem TopologicalCategory SingularCohomology
  SingularCohomologyFunctor CategoryNerve GeometricRealizationCarrier
  GeometricRealizationMaps SingularCochainReplacementEdge.
From DiazParkBLO Require Import BLODiagram BLODiagramNerve BLOEdgeAugmentation.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCohomology DPSingularCohomologyFunctor DPCategoryNerve
  DPGeometricRealization DPGeometricRealizationMaps DPSingularReplacementEdge
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPFusionCentralizerCoverProjection DPBLODiagram DPBLODiagramNerve DPBLOEdgeAugmentation.

Module DPBLOEdgeCone.
Section Diagram.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Local Notation I := (opposite (elementary_category F p)).
Local Notation D := (@space_diagram S F L p Real).
Local Notation Y := (realization_space Real (nerve (DPCentricLinking.linking_category L))).
Local Notation a := (@space_forgetful S F L p Real).
Local Notation rawK := (@raw_coefficient S F L p Real R A).

Definition forgetful_cone n : cone (rawK n)
    [the lmodType R of singular_cohomology Real Y A n].
Proof.
refine (@Build_cone (opposite I) (module_category R) (rawK n)
  [the lmodType R of singular_cohomology Real Y A n]
  (fun E => fmap (singular_cohomology_functor Real A n) (component a E)) _).
move=> E E' u; apply module_hom_ext => z.
change (singular_cohomology_map Real (fmap D u) A n
  (singular_cohomology_map Real (component a E) A n z) =
  singular_cohomology_map Real (component a E') A n z).
rewrite -singular_cohomology_composition.
have ha : compose (fmap D u) (component a E) = component a E'.
  have h := naturality a u; rewrite compose_id_right in h; exact h.
by rewrite ha.
Defined.

Definition forgetful_limit_map n : module_hom
    [the lmodType R of singular_cohomology Real Y A n]
    (module_limit_type (rawK n)) :=
  module_limit_lift (forgetful_cone n).

Theorem forgetful_limit_component n z (E : elementary_object F p) :
  module_limit_val (module_hom_fun (forgetful_limit_map n) z) E =
  singular_cohomology_map Real
    (realization_map Real (nerve_map (forgetful L (val E)))) A n z.
Proof. reflexivity. Qed.

Theorem raw_edge_is_forgetful (hD : raw_positive_limits_vanish L p Real A) n z :
  @raw_edge S F L p Real R A hD n z = module_hom_fun (forgetful_limit_map n) z.
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep => E.
by rewrite raw_edge_component forgetful_limit_component.
Qed.
End Diagram.
End DPBLOEdgeCone.
