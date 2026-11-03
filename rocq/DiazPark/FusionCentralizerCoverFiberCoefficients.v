From mathcomp Require Import all_ssreflect all_fingroup pgroup generic_quotient boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryReindex CategoryFibration
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionCentralizerMaps FusionCentralizer
  FusionCentralizerAmbient FusionSubsystemOrbit FusionCentralizerCover FusionCentralizerCoverProjection
  FusionCentralizerCoverFiberObjects FusionCentralizerCoverFiberIso.
Import DPFusion DPFusionOrbit DPFusionSubgroup DPFusionSubsystem DPFusionCentralizerCover
  DPFusionCentralizerCoverProjection DPFusionCentralizerCoverFiberObjects DPFusionCentralizerCoverFiberIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverFiberCoefficients.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation hH := (@DPFusionCentralizerAmbient.lift_allowed S F E).
Local Notation Fib := (fiber_category (functor_op (projection F p)) B).

Definition centralizer_centric_inclusion :
  functor (centric_orbit_category CF) (centric_orbit_category F).
Proof.
refine (@Build_functor (centric_orbit_category CF) (centric_orbit_category F)
  (fun P => Sub (ambient (val P)) (@ambient_centric S F p pS sat B P))
  (fun P Q f => DPFusionSubsystem.orbit_map hH f) _ _).
- move=> P; exact (@fmap_id _ _ (DPFusionSubsystem.orbit_functor hH) (val P)).
- move=> P Q R f g; exact (@fmap_compose _ _ (DPFusionSubsystem.orbit_functor hH)
    (val P) (val Q) (val R) f g).
Defined.

Theorem fiber_centric_functor_eq :
  functor_comp (category_iso_forward (@centralizer_fiber_isomorphism S F p pS sat B))
    (functor_comp (fiber_inclusion (functor_op (projection F p)) B)
      (functor_op (functor_comp (centralized_inclusion F p) (forget F p)))) =
  functor_op centralizer_centric_inclusion.
Proof.
apply (@functor_extensionality (opposite (centric_orbit_category CF))
  (opposite (centric_orbit_category F))
  (functor_comp (category_iso_forward (@centralizer_fiber_isomorphism S F p pS sat B))
    (functor_comp (fiber_inclusion (functor_op (projection F p)) B)
      (functor_op (functor_comp (centralized_inclusion F p) (forget F p)))))
  (functor_op centralizer_centric_inclusion) (Logic.eq_refl _)).
reflexivity.
Qed.

Theorem fiber_coefficient_eq (D : category) (M : functor (opposite (centric_orbit_category F)) D) :
  functor_comp (category_iso_forward (@centralizer_fiber_isomorphism S F p pS sat B))
    (functor_comp (fiber_inclusion (functor_op (projection F p)) B)
      (functor_comp (functor_op (functor_comp (centralized_inclusion F p) (forget F p))) M)) =
  functor_comp (functor_op centralizer_centric_inclusion) M.
Proof.
rewrite -(functor_comp_assoc (fiber_inclusion (functor_op (projection F p)) B)
  (functor_op (functor_comp (centralized_inclusion F p) (forget F p))) M).
rewrite -(functor_comp_assoc (category_iso_forward (@centralizer_fiber_isomorphism S F p pS sat B))
  (functor_comp (fiber_inclusion (functor_op (projection F p)) B)
    (functor_op (functor_comp (centralized_inclusion F p) (forget F p)))) M).
rewrite fiber_centric_functor_eq; reflexivity.
Qed.
End Comparison.
End DPFusionCentralizerCoverFiberCoefficients.


