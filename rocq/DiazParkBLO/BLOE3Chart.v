(** The inverse native-centralizer coefficient chart is the literal subgroup
    inclusion pullback, including the equality transport in the old wrapper. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryModules CategoryFibration
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionSubsystemOrbit
  FusionCentralizer FusionCentralizerAmbient FusionCentralizerCoverProjection.
From DiazParkV16b Require Import GroupCohomologyOrbitCoefficient GroupCohomologySubsystemCoefficient
  GroupCohomologyPullback LinkingCommaNaturality GroupCohomologyEmbeddingDiagramBase.
From DiazParkV28 Require Import RightKanCohomology.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPFusionCentralizerCoverProjection DPGroupCohomologyOrbitCoefficient
  DPGroupCohomologyPullback DPLinkingCommaNaturality DPGroupCohomologyEmbeddingDiagramBase.
Local Open Scope group_scope.

Module DPBLOE3Chart.
Lemma transported_nat_iso_inverse_component (R : pzRingType) (C : category)
    (N M M' : module_diagram R C) (h : M = M')
    (e : @isomorphism (functor_category C (module_category R)) N M) (P : C) :
  component (iso_inv (eq_rect M
    (fun T => @isomorphism (functor_category C (module_category R)) N T) e M' h)) P =
  @compose (module_category R) _ _ _
    (equality_arrow (congr1 (fun T => fobj T P) (Logic.eq_sym h)))
    (component (iso_inv e) P).
Proof. case: M' / h; rewrite /equality_arrow; exact: esym (compose_id_left _). Qed.

Lemma centralizer_coefficient_inverse_chart
    (S : finGroupType) (F : DPFusionSystem.system S) (p : nat)
    (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (n : nat) (B : elementary_object F p)
    (P : centric_object (DPFusionCentralizer.system F (val B))) :
  component (iso_inv (@DPV28RightKanCohomology.centralizer_coefficient_nat_iso S F p pS sat n B)) P =
  pull [the lmodType [the fieldType of 'F_p] of [the fieldType of 'F_p]^o]
    (subgroup_image_hom [morphism of @sgval S 'C(val B)%G] (val P)) n.
Proof.
pose K := [the fieldType of 'F_p].
pose A := [the lmodType K of K^o].
pose CF := DPFusionCentralizer.system F (val B).
pose CC := opposite (centric_orbit_category CF).
pose N := centric_coefficient CF A n.
pose M := functor_comp (functor_op (centric_inclusion CF))
  (functor_comp (functor_op (@DPFusionSubsystem.orbit_functor S F 'C(val B)%G
    CF (@DPFusionCentralizerAmbient.lift_allowed S F (val B)))) (coefficient F A n)).
pose M' := @DPV28RightKanCohomology.centralizer_restriction S F p pS sat n B.
pose h := @DPV28RightKanCohomology.centralizer_coefficient_transport_eq S F p pS sat n B.
pose e := functor_iso (precomposition (module_category K) (functor_op (centric_inclusion CF)))
  (@DPGroupCohomologySubsystemCoefficient.coefficient_nat_iso S F 'C(val B)%G CF
    (@DPFusionCentralizerAmbient.lift_allowed S F (val B)) K A n).
change (component (iso_inv (eq_rect M
  (fun T => @isomorphism (functor_category CC (module_category K)) N T) e M' h)) P =
  pull A (subgroup_image_hom [morphism of @sgval S 'C(val B)%G] (val P)) n).
rewrite transported_nat_iso_inverse_component.
have he : congr1 (fun T : module_diagram K CC => fobj T P) (Logic.eq_sym h) = Logic.eq_refl _ :=
  Prop_irrelevance _ _.
rewrite he /equality_arrow compose_id_left.
reflexivity.
Qed.
End DPBLOE3Chart.
