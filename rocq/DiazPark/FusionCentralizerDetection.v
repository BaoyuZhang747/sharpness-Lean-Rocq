(** Centralizer detection for arbitrary centric coefficient diagrams.
    All cover adjunctions, the fibration, the literal fiber isomorphism and
    its coefficient identification are the constructed concrete ones. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryIsomorphism
  CategoryModules CategoryModuleExactness CategoryFibration CategoryDerivedLimits
  CategoryDerivedIsomorphism CategoryFiberVanishing
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionCentralizer
  FusionCentralizerCover FusionCentralizerCoverProjection FusionCentralizerCoverFibration
  FusionCentralizerCoverFiberIso FusionCentralizerCoverFiberCoefficients FusionCentralizerDetectionCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionCentralizerDetectionCover.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionCentralizerDetection.
Section Detection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis ntS : [set: S] :!=: 1%G.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : pzRingType.
Variable M : module_codiagram R (DPFusionOrbit.centric_orbit_category F).

Definition centralizer_restriction (B : DPFusionCentralizerCoverProjection.elementary_object F p) :=
  functor_comp (functor_op
    (@DPFusionCentralizerCoverFiberCoefficients.centralizer_centric_inclusion S F p pS sat B)) M.

Lemma centralized_coefficient_grouping : @centralized_coefficient S F p R M =
    functor_comp (functor_op (functor_comp (DPFusionCentralizerCover.centralized_inclusion F p)
      (DPFusionCentralizerCover.forget F p))) M.
Proof.
apply (@functor_extensionality (opposite (DPFusionCentralizerCover.centralized_category F p))
  (module_category R) _ _ (Logic.eq_refl _)). reflexivity.
Qed.

Lemma centralizer_fiber_coefficient (B : DPFusionCentralizerCoverProjection.elementary_object F p) :
    functor_comp (category_iso_forward
      (@DPFusionCentralizerCoverFiberIso.centralizer_fiber_isomorphism S F p pS sat B))
      (functor_comp (fiber_inclusion (functor_op (DPFusionCentralizerCoverProjection.projection F p)) B)
        (@centralized_coefficient S F p R M)) = centralizer_restriction B.
Proof.
rewrite centralized_coefficient_grouping.
exact (@DPFusionCentralizerCoverFiberCoefficients.fiber_coefficient_eq S F p pS sat B
  (module_category R) M).
Qed.

Hypothesis centralizers_zero : forall B n (v : derived_limit R (centralizer_restriction B) n), v = 0.

Lemma centralizer_cover_fibers_zero (B : DPFusionCentralizerCoverProjection.elementary_object F p) n :
    forall v : derived_limit R
      (functor_comp (fiber_inclusion (functor_op (DPFusionCentralizerCoverProjection.projection F p)) B)
        (@centralized_coefficient S F p R M)) n, v = 0.
Proof.
pose (e := nat_iso_component (@derived_category_iso_nat_iso R
  (opposite (DPFusionOrbit.centric_orbit_category (DPFusionCentralizer.system F (val B))))
  (fiber_category (functor_op (DPFusionCentralizerCoverProjection.projection F p)) B)
  (@DPFusionCentralizerCoverFiberIso.centralizer_fiber_isomorphism S F p pS sat B) n)
  (functor_comp (fiber_inclusion (functor_op (DPFusionCentralizerCoverProjection.projection F p)) B)
    (@centralized_coefficient S F p R M))).
have ht : forall v : derived_limit R
  (functor_comp (category_iso_forward
    (@DPFusionCentralizerCoverFiberIso.centralizer_fiber_isomorphism S F p pS sat B))
    (functor_comp (fiber_inclusion (functor_op (DPFusionCentralizerCoverProjection.projection F p)) B)
      (@centralized_coefficient S F p R M))) n, v = 0.
  rewrite centralizer_fiber_coefficient. exact (@centralizers_zero B n).
intro v. apply (@module_iso_hom_injective R _ _ e).
rewrite module_hom_zero. exact: ht.
Qed.

Theorem centralizer_detection : forall n (v : derived_limit R M n), v = 0.
Proof.
have hcover : forall n (v : derived_limit R (@centralized_coefficient S F p R M) n), v = 0.
  exact (@fiberwise_derived_limit_zero R
    (opposite (DPFusionCentralizerCover.centralized_category F p))
    (opposite (opposite (DPFusionCentralizerCoverProjection.elementary_category F p)))
    (functor_op (DPFusionCentralizerCoverProjection.projection F p))
    (@DPFusionCentralizerCoverFibration.projection_op_fibration S F p sat)
    (@centralized_coefficient S F p R M) centralizer_cover_fibers_zero).
intros n v. apply (@module_iso_hom_injective R _ _
  (@centralizer_cover_derived_iso S F p pS ntS sat R M n)).
rewrite module_hom_zero. exact: hcover.
Qed.
End Detection.
End DPFusionCentralizerDetection.
