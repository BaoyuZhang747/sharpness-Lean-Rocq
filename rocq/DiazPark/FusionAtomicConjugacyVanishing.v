From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryFinite CategoryModules
  CategoryAtomicDeletionFiltration CategoryAtomicDeletionTheorem FusionSystems FusionSaturation FusionOrbit FusionFiniteCategory
  FusionAtomicUnit FusionAtomicComparison FusionRadical FusionAtomicConjugacySupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAtomicConjugacyVanishing.
Section SupportBridge.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : pzRingType.
Variable q : DPFusionOrbit.centric_object F.
Variable D : module_codiagram R (DPFusionOrbit.centric_orbit_category F).

Lemma atomic_support_orbit :
  @coefficient_atomic (DPFusionFinite.centric_finite_category F) R D q ->
  @DPFusionAtomicUnit.atomic S F (val q) R D.
Proof.
move=> h P hn; apply: h=> hPq.
pose e := @fc_iso_of_related (DPFusionFinite.centric_finite_category F) P q hPq.
exact (hn (functor_iso (DPFusionOrbit.centric_inclusion F) (iso_symm e))).
Qed.
End SupportBridge.

Section Vanishing.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : pzRingType.

(** Every nonradical centric atom vanishes in every actual derived degree;
    no full-normalization or coefficient finiteness hypothesis remains. *)
Theorem nonradical_atomic_zero (q : DPFusionOrbit.centric_object F)
    (hn : ~ DPFusionRadical.radical F p (val q))
    (D : module_codiagram R (DPFusionOrbit.centric_orbit_category F))
    (hD : @coefficient_atomic (DPFusionFinite.centric_finite_category F) R D q) :
    derived_all_zero D.
Proof.
apply: (@DPFusionAtomicConjugacySupport.atomic_vanishing_of_normalized S F R p _ q hn D hD).
move=> q0 hN hnr E hE n.
apply: (@DPFusionAtomicComparison.normalized_nonradical_atomic_zero S F p pS sat
  (val q0) (valP q0) hN R E (atomic_support_orbit hE)).
exact/negP.
Qed.
End Vanishing.
End DPFusionAtomicConjugacyVanishing.


