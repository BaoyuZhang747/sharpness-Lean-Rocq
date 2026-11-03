(** Actual atomic higher limits are compared with the p-orbit category of
    Out_F(Q).  Nonradical atoms vanish in every degree, over arbitrary rings. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup sylow.
From DiazPark Require Import Category CategoryModules CategoryNaturalIso
  CategoryDerivedLimits CategoryDerivedRan HomologicalModuleIso BarHigherLimitVanishing
  GroupOrbitPReflection GroupOrbitAtomicZero FusionSystems FusionSaturation FusionOrbit
  FusionRadical FusionAtomicFunctorPreimages FusionAtomicFunctor FusionAtomicFunctorComma
  FusionAtomicUnitGeometry FusionAtomicUnit FusionAtomicNativeRadical.
Import GRing.Theory DPFusionOrbit DiazParkHomologicalModuleIso
  DiazParkBarHigherLimitVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionAtomicComparison.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable Q : {group S}.
Hypothesis centricQ : DPFusionSystem.centric F Q.
Hypothesis normalizedQ : DPFusionSystem.fully_normalized F Q.
Local Notation CC := (centric_orbit_category F).
Local Notation B := (DPFusionAtomicFunctor.domain F p Q).
Local Notation a := (DPFusionAtomicFunctor.comparison_functor pS sat centricQ).
Local Notation family P := (@DPFusionAtomicComma.comma_initial_family S F p pS sat Q centricQ normalizedQ P).
Variable R : pzRingType.
Variable D : module_codiagram R CC.
Hypothesis atomicD : DPFusionAtomicUnit.atomic Q D.
Local Notation A := (functor_comp (functor_op a) D).

Definition atomic_derived_iso n : @isomorphism (module_category R)
    (derived_limit R D n) (derived_limit R A n) :=
  module_iso_comp
    (functor_iso (derived_limit_functor R (opposite CC) n)
      (DPFusionAtomicUnit.atomic_unit_iso pS sat centricQ normalizedQ atomicD))
    (nat_iso_component (derived_ran_nat_iso R (functor_op a) (fun P => family P) n) A).

Lemma restricted_atomic (H : B) (ntH : val H :!=: 1%G) :
    forall v : fobj A H, v = 0.
Proof.
  move=> v. apply atomicD => e.
  exact (@DPFusionAtomicGeometry.nontrivial_preimage_not_isomorphic
    S F Q centricQ (val H) (DPFusionAtomicFunctor.object_bound H) ntH e).
Qed.

Theorem normalized_nonradical_atomic_zero
    (nonradicalQ : ~~ DPFusionRadical.radical F p Q) n :
    forall q : derived_limit R D n, q = 0.
Proof.
  apply (proj2 (module_iso_zero_iff (atomic_derived_iso n))).
  exact (@DPGroupOrbitAtomic.normal_p_sylow_atomic_zero
    (DPFusionAtomicPreimages.outer_type F Q) p
    (DPFusionAtomicNativeRadical.native_pcore F p Q)
    (DPFusionAtomicNativeRadical.native_pcore_normal F p Q)
    (DPFusionAtomicNativeRadical.native_pcore_nontrivial nonradicalQ)
    (DPFusionAtomicNativeRadical.native_pcore_pgroup F p Q) R
    (DPFusionAtomicPreimages.ambient_outer F Q)
    (DPFusionAtomicPreimages.ambient_outer_sylow_subtype sat normalizedQ)
    A restricted_atomic n).
Qed.
End Comparison.
End DPFusionAtomicComparison.
