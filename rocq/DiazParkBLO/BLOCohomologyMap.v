(** Canonical natural transformation from native enlarged-category
    cohomology to the existing right Kan coefficient, with literal coordinates.
    No pointwise invertibility or centraliser comparison is assumed here. *)
From mathcomp Require Import all_boot all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleLimits CategoryNaturalIso CategoryStructured CategoryComma
  CategoryModuleRightKan FusionSystems FusionCentralizerCover
  FusionCentralizerCoverProjection FusionCentralizerDetectionCover.
From DiazParkV16b Require Import LinkingSystem CategoryNerve SingularCohomology
  CategoryConstantCohomology GroupCohomologyOrbitCoefficient GroupClassifyingCohomology
  GeometricRealizationCarrier GeometricRealizationMaps RealizationNerveCohomologyUnconditional.
From DiazParkV28 Require Import CategoryFiberRanComparison FusionCentralizerComma.
From DiazParkBLO Require Import BLODiagram BLODiagramNerve BLOCohomologyNative
  BLOCohomologyDistinguished BLOCohomologyComma.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPBLODiagram DPFusionCentralizerCoverProjection DPCategoryNerve
  DPSingularCohomology DPGeometricRealization DPGeometricRealizationMaps
  DPRealizationNerveCohomologyUnconditional DPGroupClassifyingCohomology.

Module DPBLOCohomologyMap.
Section Comparison.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation EC := (elementary_category F p).
Local Notation tau := (DPV28CentralizerComma.tau F p).
Local Notation ambient := (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n).
Local Notation coeff := (@DPFusionCentralizerDetectionCover.centralized_coefficient S F p R ambient).
Local Notation native := (@DPBLOCohomologyNative.native_coefficient Real S F L p R A n).
Local Notation bar := (@DPBLOCohomologyNative.bar_coefficient S F L p R A n).

Definition ran_coefficient : module_diagram R EC :=
  functor_comp (DPV28FiberRanComparison.to_double_opposite EC)
    (fobj (module_ran R tau) coeff).

Definition bar_ran_trans : nat_trans bar ran_coefficient :=
  @Build_nat_trans EC (module_category R) bar ran_coefficient
    (@DPBLOCohomologyComma.bar_to_ran S F L p R A n)
    (@DPBLOCohomologyComma.bar_to_ran_natural S F L p R A n).

Definition native_ran_trans : nat_trans native ran_coefficient :=
  nat_comp (iso_hom (@DPBLOCohomologyNative.native_bar_nat_iso Real S F L p R A n))
    bar_ran_trans.

Definition native_to_ran (E : EC) : module_hom (fobj native E) (fobj ran_coefficient E) :=
  component native_ran_trans E.

Lemma native_to_ran_naturality (E E' : EC) (u : hom EC E E') :
    module_hom_comp (fmap native u) (native_to_ran E') =
    module_hom_comp (native_to_ran E) (fmap ran_coefficient u).
Proof. exact (naturality native_ran_trans u). Qed.

Lemma native_to_ran_coordinate (E : EC) (x : fobj native E)
    (X : structured_category tau E) :
    module_limit_val (native_to_ran E x) X =
    DPCategoryConstantCohomology.pull A (DPBLOCohomologyComma.comma_distinguished L X) n
      (module_hom_fun (iso_hom (comparison_iso_unconditional Real A
        (enlarged_category L (val E)) n)) x).
Proof. reflexivity. Qed.

Lemma native_to_ran_singular_coordinate (E : EC) (x : fobj native E)
    (X : structured_category tau E) :
    module_limit_val (native_to_ran E x) X =
    module_hom_fun (iso_hom (group_comparison_iso Real A
      [the finGroupType of [subg (DPFusionCentralizerCover.carrier (val (structured_source X)))]%type] n))
      (singular_cohomology_map Real
        (realization_map Real (nerve_map (DPBLOCohomologyComma.comma_distinguished L X))) A n x).
Proof.
rewrite native_to_ran_coordinate.
symmetry; exact: comparison_iso_unconditional_natural.
Qed.
End Comparison.
End DPBLOCohomologyMap.
