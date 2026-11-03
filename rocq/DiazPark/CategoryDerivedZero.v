(** Pointwise zero diagrams have zero genuine derived limits in every degree. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex HomologicalCohomology
  BarComplex BarHigherLimitVanishing BarInjectiveComparisonAll.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkBarComplex
  DiazParkBarHigherLimitVanishing DiazParkBarInjectiveComparisonAll.
Local Open Scope ring_scope.

Theorem pointwise_zero_derived_limits (R : pzRingType) (C : category)
    (D : module_codiagram R C)
    (zeroD : forall x (v : fobj D x), v = 0) n :
    forall q : derived_limit R D n, q = 0.
Proof.
  apply/(module_iso_zero_iff (bar_chosen_injective_cohomology_iso D n)).
  move=> q. have [z <-] := quotient_pi_surjective q.
  have hz : z = 0.
    apply submodule_val_injective.
    apply functional_extensionality_dep => x.
    apply functional_extensionality_dep => path.
    exact (zeroD x (val z x path)).
  rewrite hz. exact: linear0.
Qed.
