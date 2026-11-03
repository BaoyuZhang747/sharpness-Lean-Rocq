(** The right Kan extension of native mod-p cohomology to the elementary
    category. Its arrows are the actual Ran arrows. No degree-zero vanishing
    and no centralizer linking-system decomposition is asserted or used. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup abelian zmodp boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryIsomorphism CategoryIsomorphismAdjunction CategoryModules CategoryModuleExactness
  CategoryModuleLimits CategoryModuleLimitFunctor CategoryModuleRightKan CategoryModuleFiberKan
  CategoryDerivedLimits CategoryDerivedIsomorphism CategoryFibration HomologicalModuleIso
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionSubsystemOrbit
  FusionCentralizer FusionCentralizerAmbient FusionCentralizerSaturation
  FusionCentralizerCover FusionCentralizerCoverProjection FusionCentralizerCoverFiberCoefficients
  FusionCentralizerDetectionCover.
From DiazParkV16b Require Import GroupCohomologyOrbitCoefficient GroupCohomologySubsystemCoefficient.
From DiazParkV28 Require Import CategoryFiberRanComparison FusionCentralizerComma
  FusionCentralizerRouteB GroupCohomologyRouteB.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPFusionOrbit
  DPFusionCentralizerCoverProjection DPGroupCohomologyOrbitCoefficient.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV28RightKanCohomology.
Section Cohomology.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable n : nat.
Local Notation K := [the fieldType of 'F_p].
Local Notation A := [the lmodType K of K^o].
Local Notation tau := (DPV28CentralizerComma.tau F p).

Definition ambient_cohomology := centric_coefficient F A n.

Definition cover_cohomology :=
  @DPFusionCentralizerDetectionCover.centralized_coefficient S F p K ambient_cohomology.

Definition ran_cohomology := fobj (module_ran K tau) cover_cohomology.

(** The identity-on-objects-and-arrows category isomorphism explicitly removes
    the double opposite in the accepted cover projection's codomain. *)
Definition H_n : module_diagram K (elementary_category F p) :=
  functor_comp (DPV28FiberRanComparison.to_double_opposite (elementary_category F p))
    ran_cohomology.

Lemma H_n_object (B : elementary_object F p) :
  fobj H_n B = fobj (fobj (module_ran K tau) cover_cohomology) B.
Proof. reflexivity. Qed.

Lemma H_n_map (B C : elementary_object F p) (a : hom (elementary_category F p) B C) :
  fmap H_n a = fmap (fobj (module_ran K tau) cover_cohomology) a.
Proof. reflexivity. Qed.

Definition centralizer_restriction (B : elementary_object F p) :=
  @DPV28CentralizerRouteB.centralizer_restriction S F p pS sat K ambient_cohomology B.

Lemma centralizer_coefficient_transport_eq (B : elementary_object F p) :
  functor_comp (functor_op (centric_inclusion (DPFusionCentralizer.system F (val B))))
    (functor_comp (functor_op (@DPFusionSubsystem.orbit_functor S F 'C(val B)%G
      (DPFusionCentralizer.system F (val B)) (@DPFusionCentralizerAmbient.lift_allowed S F (val B))))
      (coefficient F A n)) = centralizer_restriction B.
Proof.
apply (@CategoryIsomorphism.functor_extensionality
  (opposite (centric_orbit_category (DPFusionCentralizer.system F (val B))))
  (module_category K) _ _ (Logic.eq_refl _)); reflexivity.
Qed.

Definition centralizer_coefficient_nat_iso (B : elementary_object F p) :
  @isomorphism (functor_category
    (opposite (centric_orbit_category (DPFusionCentralizer.system F (val B)))) (module_category K))
    (centric_coefficient (DPFusionCentralizer.system F (val B)) A n)
    (centralizer_restriction B).
Proof.
rewrite -(centralizer_coefficient_transport_eq B).
exact (functor_iso
  (precomposition (module_category K) (functor_op (centric_inclusion (DPFusionCentralizer.system F (val B)))))
  (@DPGroupCohomologySubsystemCoefficient.coefficient_nat_iso S F 'C(val B)%G
    (DPFusionCentralizer.system F (val B)) (@DPFusionCentralizerAmbient.lift_allowed S F (val B)) K A n)).
Defined.

Definition fibre_cohomology (B : elementary_object F p) :=
  functor_comp (fiber_inclusion tau B) cover_cohomology.

Lemma centralizer_fibre_coefficient (B : elementary_object F p) :
  functor_comp (category_iso_forward (@DPV28CentralizerComma.centralizer_fiber_iso S F p sat pS B))
    (fibre_cohomology B) = centralizer_restriction B.
Proof. exact (@DPV28CentralizerRouteB.centralizer_fiber_coefficient S F p pS sat K ambient_cohomology B). Qed.

Definition fibre_centralizer_limit_iso (B : elementary_object F p) :
  @isomorphism (module_category K) (module_limit_type (fibre_cohomology B))
    (module_limit_type (centralizer_restriction B)).
Proof.
rewrite -(centralizer_fibre_coefficient B).
exact (nat_iso_component (module_left_adjoint_limit_nat_iso K
  (category_iso_adjunction (@DPV28CentralizerComma.centralizer_fiber_iso S F p sat pS B)))
  (fibre_cohomology B)).
Defined.

(** Pointwise comparison with the literal restricted ambient coefficient. *)
Definition pointwise_restricted_limit_iso (B : elementary_object F p) :
  @isomorphism (module_category K) (fobj H_n B)
    (module_limit_type (centralizer_restriction B)) :=
  module_iso_comp
    (module_ran_fiber_iso K (@DPV28CentralizerComma.tau_fibration S F p sat) B cover_cohomology)
    (fibre_centralizer_limit_iso B).

(** Pointwise comparison with the native centralizer cohomology diagram, using its actual
    coefficient natural isomorphism before passing to the ordinary limit. *)
Definition pointwise_native_limit_iso (B : elementary_object F p) :
  @isomorphism (module_category K) (fobj H_n B)
    (module_limit_type (centric_coefficient (DPFusionCentralizer.system F (val B)) A n)) :=
  module_iso_comp (pointwise_restricted_limit_iso B)
    (functor_iso (module_limit_functor K _) (iso_symm (centralizer_coefficient_nat_iso B))).

Lemma centralizer_positive_limits_zero (B : elementary_object F p) (j : nat) :
  forall v : derived_limit K (centralizer_restriction B) j.+1, v = 0.
Proof.
have /and3P[ntE elE fcE] := valP B.
have abE : abelian (val B) := abelem_abelian elE.
have pC := @DPFusionCentralizerSaturation.centralizer_pgroup S (val B) p pS.
have satC := @DPFusionCentralizerSaturation.centralizer_saturated S F (val B) abE p pS sat fcE.
pose e := functor_iso (derived_limit_functor K _ j.+1) (iso_symm (centralizer_coefficient_nat_iso B)).
intro v; apply (@module_iso_hom_injective K _ _ e).
rewrite module_hom_zero.
exact (@DPV28GroupCohomologySharpness.prime_field_higher_limits_zero _
  (DPFusionCentralizer.system F (val B)) p hp pC satC A n j _).
Qed.

Lemma fibre_positive_limits_zero (B : elementary_object F p) (j : nat) :
  forall v : derived_limit K (fibre_cohomology B) j.+1, v = 0.
Proof.
pose e := nat_iso_component (derived_category_iso_nat_iso K
  (@DPV28CentralizerComma.centralizer_fiber_iso S F p sat pS B) j.+1) (fibre_cohomology B).
have ht : forall v : derived_limit K
  (functor_comp (category_iso_forward (@DPV28CentralizerComma.centralizer_fiber_iso S F p sat pS B))
    (fibre_cohomology B)) j.+1, v = 0.
  rewrite centralizer_fibre_coefficient; exact: centralizer_positive_limits_zero.
intro v; apply (@module_iso_hom_injective K _ _ e).
rewrite module_hom_zero; exact: ht.
Qed.

Hypothesis ntS : [set: S] :!=: 1%G.

(** The all-degree comparison includes degree zero. *)
Definition higher_limit_comparison (s : nat) :
  @isomorphism (module_category K) (derived_limit K H_n s)
    (derived_limit K ambient_cohomology s) :=
  module_iso_comp
    (iso_symm (nat_iso_component (derived_category_iso_nat_iso K
      (DPV28FiberRanComparison.double_opposite_iso (elementary_category F p)) s) ran_cohomology))
    (module_iso_comp
      (@DPV28FiberRanComparison.fibre_acyclic_higher_limit_iso K _ _ tau
        (@DPV28CentralizerComma.tau_fibration S F p sat) cover_cohomology fibre_positive_limits_zero s)
      (iso_symm (@DPFusionCentralizerDetectionCover.centralizer_cover_derived_iso
        S F p pS ntS sat K ambient_cohomology s))).

Theorem successor_higher_limits_zero (j : nat) :
  forall v : derived_limit K H_n j.+1, v = 0.
Proof.
intro v; apply (@module_iso_hom_injective K _ _ (higher_limit_comparison j.+1)).
rewrite module_hom_zero.
exact (@DPV28GroupCohomologySharpness.prime_field_higher_limits_zero S F p hp pS sat A n j _).
Qed.

(** Vanishing in every positive degree. *)
Theorem positive_higher_limits_zero (s : nat) :
  (0 < s)%N -> forall v : derived_limit K H_n s, v = 0.
Proof. case: s => [|j] // _; exact: successor_higher_limits_zero. Qed.

End Cohomology.
End DPV28RightKanCohomology.
