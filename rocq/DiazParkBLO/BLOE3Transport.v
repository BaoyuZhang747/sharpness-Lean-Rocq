(** Generic transport helper for BLO-02.  The final native endpoint must
    instantiate e with the actually constructed native-to-Ran natural iso. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryModuleExactness CategoryDerivedLimits HomologicalModuleIso
  FusionSystems FusionSaturation FusionCentralizerCoverProjection.
From DiazParkV28 Require Import RightKanCohomology.
From DiazParkBLO Require Import BLOE3Core.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPFusionCentralizerCoverProjection.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPBLOE3Transport.
Section Transport.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable n : nat.
Hypothesis ntS : [set: S] :!=: 1%G.
Local Notation K := [the fieldType of 'F_p].
Variable N : module_diagram K (elementary_category F p).
Variable e : @isomorphism (functor_category (elementary_category F p) (module_category K))
  N (@DPV28RightKanCohomology.H_n S F p n).

Definition higher_limit_comparison (s : nat) : @isomorphism (module_category K)
  (derived_limit K N s)
  (derived_limit K (@DPV28RightKanCohomology.ambient_cohomology S F p n) s) :=
  module_iso_comp (functor_iso (derived_limit_functor K _ s) e)
    (@DPBLOE3.higher_limit_comparison S F p hp pS sat n ntS s).

Theorem positive_higher_limits_zero (s : nat) (hs : (0 < s)%N) :
  forall v : derived_limit K N s, v = 0.
Proof.
intro v; apply (@module_iso_hom_injective K _ _ (functor_iso (derived_limit_functor K _ s) e)).
rewrite module_hom_zero.
exact (@DPBLOE3.positive_higher_limits_zero S F p hp pS sat n ntS s hs _).
Qed.

End Transport.
End DPBLOE3Transport.
