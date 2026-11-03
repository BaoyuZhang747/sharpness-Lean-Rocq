(** Literal geometric coordinates of the normalizer-fibre comparison.
    The native group value is reached by singular pullback along the
    actual one-object chart, followed by the unconditional group comparison. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryComma CategoryIsomorphism CategoryModules
  HomologicalModuleIso HomologicalCohomology MackeyModuleCarriers MackeyModuleQuotient FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndexCategory NormalizerLinkingChainCategory NormalizerLinkingChainProjection
  NormalizerLinkingChainEvaluation NormalizerLinkingChainAutomorphismChart
  NormalizerLinkingCommaReflection NormalizerLinkingCommaAdjunction NormalizerLinkingCommaNaturality
  NormalizerLinkingCommaCohomology CategoryConstantCohomology GroupCohomologyBase
  CategoryNerve SingularCohomology GeometricRealizationMaps RealizationNerveCohomology
  RealizationNerveCohomologyUnconditional GroupClassifyingCohomology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomologicalModuleIso DiazParkCohomology DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainIndex DPNormalizerLinkingChainCategory DPNormalizerLinkingChainAutomorphismChart
  DPNormalizerLinkingCommaReflection DPNormalizerLinkingCommaAdjunction DPCategoryNerve
  DPSingularCohomology DPGeometricRealizationMaps DPRealizationNerveCohomology
  DPRealizationNerveCohomologyUnconditional DPGroupClassifyingCohomology.

Module DPNormalizerLinkingRealizationCoordinates.
Section Coordinates.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable d : index_category F.
Variable r : chain F.
Hypothesis hr : chain_class r = d.
Variable n : nat.
Local Notation P := (DPNormalizerLinkingChainProjection.projection L).
Local Notation C := (costructured_category P d).
Local Notation G := (chain_automorphism_group L r).
Local Notation J := (@comparison S F L d r hr).

Definition fibre_native_iso : @isomorphism (module_category R)
    [the lmodType R of singular_cohomology Real (classifying_space Real C) A n]
    (DPGroupCohomology.value R G A n) :=
  module_iso_comp (comparison_iso_unconditional Real A C n)
    (DPCategoryConstantCohomology.adjunction_iso A (@comparison_adjunction S F L d r hr) n).

Theorem fibre_native_iso_forward (x : singular_cohomology Real (classifying_space Real C) A n) :
    module_hom_fun (iso_hom fibre_native_iso) x =
    module_hom_fun (iso_hom (group_comparison_iso Real A G n))
      (singular_cohomology_map Real (realization_map Real (nerve_map J)) A n x).
Proof.
change (module_hom_fun (DPCategoryConstantCohomology.pull A J n)
  (module_hom_fun (iso_hom (comparison_iso_unconditional Real A C n)) x) =
  module_hom_fun (iso_hom (comparison_iso_unconditional Real A (DPGroupCohomology.group_category G) n))
    (singular_cohomology_map Real (realization_map Real (nerve_map J)) A n x)).
symmetry; exact: comparison_iso_unconditional_natural.
Qed.

Theorem fibre_native_cocone_coordinate (D : category) (E : functor (chain_category L) D)
    (x : singular_cohomology Real (classifying_space Real D) A n) :
    module_hom_fun (iso_hom fibre_native_iso)
      (singular_cohomology_map Real
        (realization_map Real (nerve_map (functor_comp (costructured_projection P d) E))) A n x) =
    module_hom_fun (iso_hom (group_comparison_iso Real A G n))
      (singular_cohomology_map Real
        (realization_map Real (nerve_map (functor_comp (automorphism_chart L r) E))) A n x).
Proof.
change (module_hom_fun (DPCategoryConstantCohomology.pull A J n)
  (module_hom_fun (iso_hom (comparison_iso_unconditional Real A C n))
    (singular_cohomology_map Real
      (realization_map Real (nerve_map (functor_comp (costructured_projection P d) E))) A n x)) =
  module_hom_fun (iso_hom (group_comparison_iso Real A G n))
    (singular_cohomology_map Real
      (realization_map Real (nerve_map (functor_comp (automorphism_chart L r) E))) A n x)).
rewrite comparison_iso_unconditional_natural.
change (module_hom_fun (module_hom_comp
  (DPCategoryConstantCohomology.pull A (functor_comp (costructured_projection P d) E) n)
  (DPCategoryConstantCohomology.pull A J n))
  (module_hom_fun (iso_hom (comparison_iso_unconditional Real A D n)) x) =
  module_hom_fun (iso_hom (group_comparison_iso Real A G n))
    (singular_cohomology_map Real
      (realization_map Real (nerve_map (functor_comp (automorphism_chart L r) E))) A n x)).
rewrite -DPCategoryConstantCohomology.pull_composition -functor_comp_assoc
  DPNormalizerLinkingCommaNaturality.comparison_forget.
symmetry; exact: comparison_iso_unconditional_natural.
Qed.

Theorem fibre_native_evaluation_coordinate
    (x : singular_cohomology Real (classifying_space Real (DPCentricLinking.linking_category L)) A n) :
    module_hom_fun (iso_hom fibre_native_iso)
      (singular_cohomology_map Real
        (realization_map Real (nerve_map (functor_comp (costructured_projection P d)
          (DPNormalizerLinkingChainEvaluation.evaluation L)))) A n x) =
    module_hom_fun (iso_hom (group_comparison_iso Real A G n))
      (singular_cohomology_map Real
        (realization_map Real (nerve_map (functor_comp (automorphism_chart L r)
          (DPNormalizerLinkingChainEvaluation.evaluation L)))) A n x).
Proof. exact: fibre_native_cocone_coordinate. Qed.
End Coordinates.

Section Representatives.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Variables n : nat.

Theorem fibre_native_iso_agreement (d : index_category F) :
    @fibre_native_iso Real R A S F L d (r d) (hr d) n =
    module_iso_comp
      (comparison_iso_unconditional Real A
        (costructured_category (DPNormalizerLinkingChainProjection.projection L) d) n)
      (@DPNormalizerLinkingCommaCohomology.comparison_iso R A S F L r hr n d).
Proof. reflexivity. Qed.
End Representatives.
End DPNormalizerLinkingRealizationCoordinates.
