(** Coordinates of the accepted pointwise Ran/native-centralizer comparison.
    These identify its actual map and are used to prove invertibility of the
    new native enlarged-category comparison. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryIsomorphism CategoryIsomorphismAdjunction CategoryAdjunction
  CategoryLimits CategoryLimitMaps CategoryLimitFunctor CategoryComma CategoryStructured
  CategoryFibration CategoryFiberRan CategoryModules CategoryModuleLimits CategoryModuleLimitFunctor
  CategoryModuleRightKan CategoryModuleFiberKan HomologicalModuleIso
  FusionSystems FusionSaturation FusionOrbit FusionCentralizer FusionCentralizerCover
  FusionCentralizerCoverProjection FusionCentralizerCoverFiberObjects FusionCentralizerCoverFiberIso.
From DiazParkV16b Require Import GroupCohomologyOrbitCoefficient.
From DiazParkV28 Require Import FusionCentralizerComma RightKanCohomology.
From DiazParkBLO Require Import BLOE3Limits.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPFusionOrbit
  DPFusionCentralizerCoverProjection DPGroupCohomologyOrbitCoefficient.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPBLOE3Pointwise.

Lemma transported_limit_iso_coordinate (R : pzRingType) (C : category)
    (F G : module_diagram R C) (h : F = G) (U : lmodType R)
    (e : @isomorphism (module_category R) U (module_limit_type F)) (P : C) :
  compose (iso_hom (eq_rect F
    (fun T => @isomorphism (module_category R) U (module_limit_type T)) e G h))
    (module_limit_projection G P) =
  compose (compose (iso_hom e) (module_limit_projection F P))
    (equality_arrow (congr1 (fun T => fobj T P) h)).
Proof. case: G / h; rewrite /equality_arrow; exact: esym (compose_id_right _). Qed.

Lemma module_limit_map_coordinate (R : pzRingType) (C : category)
    (F G : module_diagram R C) (a : nat_trans F G) (P : C) :
  compose (fmap (module_limit_functor R C) a) (module_limit_projection G P) =
  @compose (module_category R) _ _ _ (module_limit_projection F P) (component a P).
Proof. exact: limit_map_fac. Qed.

Section Pointwise.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable n : nat.
Variable B : elementary_object F p.
Local Notation K := [the fieldType of 'F_p].
Local Notation A := [the lmodType K of K^o].
Local Notation CF := (DPFusionCentralizer.system F (val B)).
Local Notation CC := (opposite (centric_orbit_category CF)).
Local Notation tau := (DPV28CentralizerComma.tau F p).
Local Notation cover := (@DPV28RightKanCohomology.cover_cohomology S F p n).
Local Notation fibre := (@DPV28RightKanCohomology.fibre_cohomology S F p n B).
Local Notation restriction := (@DPV28RightKanCohomology.centralizer_restriction S F p pS sat n B).
Local Notation Hn := (@DPV28RightKanCohomology.H_n S F p n).
Local Notation fi := (@DPV28CentralizerComma.centralizer_fiber_iso S F p sat pS B).
Local Notation local_fibre := (@DPFusionCentralizerCoverFiberObjects.fiber_of_local S F p pS sat B).

Definition local_comma_point (P : centric_object CF) : structured_category tau B :=
  fiber_structured_point (local_fibre P).

Lemma local_comma_source (P : centric_object CF) :
  structured_source (local_comma_point P) =
    @DPFusionCentralizerCoverFiberObjects.centralized_of_local S F p pS sat B P.
Proof. reflexivity. Qed.

Lemma local_comma_is_kappa (P : centric_object CF) :
  local_comma_point P = fobj (@DPV28CentralizerComma.kappa_E S F p B) (local_fibre P).
Proof. reflexivity. Qed.

Lemma centralizer_fibre_coordinate (P : centric_object CF) :
  compose (iso_hom (@DPV28RightKanCohomology.fibre_centralizer_limit_iso S F p pS sat n B))
    (module_limit_projection restriction P) =
  module_limit_projection fibre (local_fibre P).
Proof.
pose h := @DPV28RightKanCohomology.centralizer_fibre_coefficient S F p pS sat n B.
pose e := nat_iso_component (module_left_adjoint_limit_nat_iso K (category_iso_adjunction fi)) fibre.
change (compose (iso_hom (eq_rect (functor_comp (category_iso_forward fi) fibre)
  (fun T => @isomorphism (module_category K) (module_limit_type fibre) (module_limit_type T))
  e restriction h)) (module_limit_projection restriction P) =
  module_limit_projection fibre (local_fibre P)).
rewrite transported_limit_iso_coordinate.
have he : congr1 (fun T : module_diagram K CC => fobj T P) h = Logic.eq_refl _ :=
  Prop_irrelevance _ _.
rewrite he /equality_arrow compose_id_right.
exact (@DPBLOE3Limits.module_adjoint_limit_coordinate K _ _ _ _
  (category_iso_adjunction fi) fibre P).
Qed.

Lemma pointwise_restricted_coordinate (P : centric_object CF) :
  compose (iso_hom (@DPV28RightKanCohomology.pointwise_restricted_limit_iso S F p pS sat n B))
    (module_limit_projection restriction P) =
  module_limit_projection (functor_comp (structured_projection tau B) cover) (local_comma_point P).
Proof.
change (compose (compose
  (iso_hom (module_ran_fiber_iso K (@DPV28CentralizerComma.tau_fibration S F p sat) B cover))
  (iso_hom (@DPV28RightKanCohomology.fibre_centralizer_limit_iso S F p pS sat n B)))
  (module_limit_projection restriction P) =
  module_limit_projection (functor_comp (structured_projection tau B) cover) (local_comma_point P)).
rewrite compose_assoc centralizer_fibre_coordinate.
exact (@module_ran_fiber_iso_coordinate K _ _ tau
  (@DPV28CentralizerComma.tau_fibration S F p sat) B cover (local_fibre P)).
Qed.

Lemma pointwise_native_coordinate (P : centric_object CF) :
  compose (iso_hom (@DPV28RightKanCohomology.pointwise_native_limit_iso S F p pS sat n B))
    (module_limit_projection (centric_coefficient CF A n) P) =
  @compose (module_category K) _ _ _ (module_limit_projection (functor_comp (structured_projection tau B) cover) (local_comma_point P))
    (component (iso_inv (@DPV28RightKanCohomology.centralizer_coefficient_nat_iso S F p pS sat n B)) P).
Proof.
pose a := iso_hom (@DPV28RightKanCohomology.pointwise_restricted_limit_iso S F p pS sat n B).
pose b := fmap (module_limit_functor K CC)
  (iso_inv (@DPV28RightKanCohomology.centralizer_coefficient_nat_iso S F p pS sat n B)).
pose d := module_limit_projection (centric_coefficient CF A n) P.
change (compose (compose a b) d =
  @compose (module_category K) _ _ _ (module_limit_projection (functor_comp (structured_projection tau B) cover) (local_comma_point P))
    (component (iso_inv (@DPV28RightKanCohomology.centralizer_coefficient_nat_iso S F p pS sat n B)) P)).
rewrite (compose_assoc a b d) module_limit_map_coordinate.
rewrite -compose_assoc pointwise_restricted_coordinate; reflexivity.
Qed.

End Pointwise.
End DPBLOE3Pointwise.
