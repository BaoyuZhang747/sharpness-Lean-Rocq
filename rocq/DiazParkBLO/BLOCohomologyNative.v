(** Native singular cohomology of the actual enlarged-category diagram,
    and its natural constant-category-bar comparison in every degree. *)
From mathcomp Require Import all_boot all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryNaturalIso
  FusionSystems FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem CategoryNerve SingularCohomology
  SingularCochainReplacementEdge CategoryConstantCohomology
  GeometricRealizationCarrier GeometricRealizationMaps
  RealizationNerveCohomologyUnconditional.
From DiazParkV28 Require Import CategoryFiberRanComparison.
From DiazParkBLO Require Import BLODiagram BLODiagramNerve.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPBLODiagram DPBLODiagramNerve DPFusionCentralizerCoverProjection
  DPCategoryNerve DPSingularCohomology DPSingularReplacementEdge
  DPGeometricRealization DPGeometricRealizationMaps
  DPRealizationNerveCohomologyUnconditional.

Module DPBLOCohomologyNative.
Section Native.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation EC := (elementary_category F p).

Definition raw_coefficient : module_diagram R (opposite (opposite EC)) :=
  singular_cohomology_diagram Real A (space_diagram L p Real) n.

Definition native_coefficient : module_diagram R EC :=
  functor_comp (DPV28FiberRanComparison.to_double_opposite EC) raw_coefficient.

Lemma native_coefficient_object (E : EC) : (fobj native_coefficient E : Type) =
    singular_cohomology Real
      (realization_space Real (nerve (enlarged_category L (val E)))) A n.
Proof. reflexivity. Qed.

Lemma native_coefficient_arrow (E E' : EC) (u : hom EC E E')
    (x : fobj native_coefficient E) :
    module_hom_fun (fmap native_coefficient u) x =
      singular_cohomology_map Real (realization_map Real (nerve_map (precompose L u))) A n x.
Proof. reflexivity. Qed.

Definition bar_coefficient : module_diagram R EC.
Proof.
refine (@Build_functor EC (module_category R)
  (fun E => DPCategoryConstantCohomology.value R A (enlarged_category L (val E)) n)
  (fun E E' u => DPCategoryConstantCohomology.pull A (precompose L u) n) _ _).
- move=> E; rewrite precompose_identity; exact: DPCategoryConstantCohomology.pull_identity.
- move=> E E' E'' u v; rewrite precompose_composition.
  exact: DPCategoryConstantCohomology.pull_composition.
Defined.

Definition native_bar_component (E : EC) : @isomorphism (module_category R)
    (fobj native_coefficient E) (fobj bar_coefficient E) :=
  comparison_iso_unconditional Real A (enlarged_category L (val E)) n.

Lemma native_bar_naturality (E E' : EC) (u : hom EC E E') :
    module_hom_comp (fmap native_coefficient u) (iso_hom (native_bar_component E')) =
    module_hom_comp (iso_hom (native_bar_component E)) (fmap bar_coefficient u).
Proof.
apply module_hom_ext=> x.
exact: comparison_iso_unconditional_natural.
Qed.

Definition native_bar_nat_iso :
    @isomorphism (functor_category EC (module_category R)) native_coefficient bar_coefficient :=
  @nat_iso_of_components EC (module_category R) native_coefficient bar_coefficient
    native_bar_component native_bar_naturality.

Lemma native_bar_nat_iso_component (E : EC) :
    component (iso_hom native_bar_nat_iso) E = iso_hom (native_bar_component E).
Proof. reflexivity. Qed.
End Native.
End DPBLOCohomologyNative.
