(** The actual centralizer cover preserves native derived limits, with no
    cover-equivalence or derived-comparison hypothesis. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryAdjunction
  CategoryModules CategoryDerivedLimits CategoryDerivedAdjunction HomologicalModuleIso
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionCentralizerCover
  FusionCentralizerCoverOmega FusionCentralizerCoverEquivalence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionCentralizerDetectionCover.
Section Cover.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis ntS : [set: S] :!=: 1%G.
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : pzRingType.
Variable M : module_codiagram R (DPFusionOrbit.centric_orbit_category F).

Definition cover_coefficient := functor_comp
  (functor_op (DPFusionCentralizerCover.forget F p)) M.

Definition centralized_coefficient := functor_comp
  (functor_op (DPFusionCentralizerCover.centralized_inclusion F p)) cover_coefficient.

Definition centralizer_cover_derived_iso n : @isomorphism (module_category R)
    (derived_limit R M n) (derived_limit R centralized_coefficient n) :=
  module_iso_comp
    (nat_iso_component (derived_left_adjoint_nat_iso R
      (adjunction_op (@DPFusionCentralizerCoverOmega.section_forget_adjunction S F p pS ntS)) n) M)
    (nat_iso_component (derived_left_adjoint_nat_iso R
      (adjunction_op (@DPFusionCentralizerCoverEquivalence.centralized_inclusion_right_adjoint S F p sat)) n)
      cover_coefficient).

End Cover.
End DPFusionCentralizerDetectionCover.
