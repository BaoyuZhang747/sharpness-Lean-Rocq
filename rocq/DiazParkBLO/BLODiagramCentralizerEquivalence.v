(** An actual equivalence between the constructed centraliser linking
    category and BLO's enlarged category. The inverse, unit and counit are
    built from the proved saturation straightening linking isomorphisms. *)
From mathcomp Require Import all_boot all_fingroup pgroup.
From DiazPark Require Import Category CategoryReindex CategoryAdjunction
  FusionSystems FusionSaturation FusionOrbit FusionCentralizer FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem.
From DiazParkBLO Require Import BLODiagram BLODiagramCentralizerBase
  BLODiagramCentralizerObjects BLODiagramCentralizerSystem
  BLODiagramCentralizerCompatibility BLODiagramReindexEquivalence.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPFusionCentralizerCoverProjection DPBLODiagram
  DPBLOCentralizerBase DPBLOCentralizerSystem.
Local Open Scope group_scope.

Module DPBLOCentralizerEquivalence.
Section Equivalence.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation Obj := (centric_object CF).
Local Notation CL := (@centralizer_linking_system S F L p pS sat B).
Local Notation C := (DPCentricLinking.linking_category CL).
Local Notation D := (enlarged_category L E).
Local Notation J := (@centralizer_inclusion S F L p pS sat B).
Local Notation i := (@centralizer_point S F p pS sat B).
Local Notation r := (@DPBLOCentralizerObjects.target_object S F p sat B).
Local Notation e := (@DPBLOCentralizerObjects.straightening_iso S F L p pS sat B).

Definition centralizer_retraction : functor D C :=
  @DPBLOReindexEquivalence.inverse_functor D Obj i r e.

Definition centralizer_adjunction : adjunction J centralizer_retraction :=
  @DPBLOReindexEquivalence.reindex_adjunction D Obj i r e.

Lemma centralizer_retraction_object X : fobj centralizer_retraction X = r X.
Proof. reflexivity. Qed.

Lemma centralizer_retraction_arrow X Y (f : hom D X Y) :
    fmap centralizer_retraction f =
    @Category.compose D _ _ _ (iso_inv (e X)) (Category.compose f (iso_hom (e Y))).
Proof. reflexivity. Qed.

Lemma centralizer_unit_component P :
    component (adj_unit centralizer_adjunction) P = iso_hom (e (i P)).
Proof. reflexivity. Qed.

Lemma centralizer_counit_component X :
    component (adj_counit centralizer_adjunction) X = iso_inv (e X).
Proof. reflexivity. Qed.

Definition centralizer_unit_iso (P : Obj) : @isomorphism C P (r (i P)) :=
  @DPBLOReindexEquivalence.unit_iso D Obj i r e P.

Definition centralizer_counit_iso (X : D) : @isomorphism D (i (r X)) X :=
  @DPBLOReindexEquivalence.counit_iso D Obj i r e X.

Lemma centralizer_unit_iso_hom P :
    iso_hom (centralizer_unit_iso P) = component (adj_unit centralizer_adjunction) P.
Proof. reflexivity. Qed.

Lemma centralizer_counit_iso_hom X :
    iso_hom (centralizer_counit_iso X) = component (adj_counit centralizer_adjunction) X.
Proof. reflexivity. Qed.
End Equivalence.
End DPBLOCentralizerEquivalence.
