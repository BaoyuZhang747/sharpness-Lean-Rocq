From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology.
Local Open Scope ring_scope.

Module DiazParkHomologicalDegreeZero.
Section Zero.
Variable R : pzRingType.
Variable K : @cochain_complex R.

Lemma zero_boundary_cycle_zero (z : cycle_module K 0) :
  boundaries_in_cycles K 0 z -> z = 0.
Proof. move=> hz; apply submodule_val_injective; exact: hz. Qed.

Definition cohomology_zero_cycle :
    {linear cohomology K 0 -> cycle_module K 0} :=
  (@quotient_lift R (cycle_module K 0) (boundaries_in_cycles K 0)
    (cycle_module K 0) (idfun : {linear cycle_module K 0 -> cycle_module K 0})
    zero_boundary_cycle_zero : {linear cohomology K 0 -> cycle_module K 0}).

Lemma cohomology_zero_cycle_pi (z : cycle_module K 0) :
  cohomology_zero_cycle (quotient_pi (boundaries_in_cycles K 0) z) = z.
Proof. exact: quotient_lift_pi. Qed.

Lemma cohomology_zero_pi_cycle (z : cohomology K 0) :
  quotient_pi (boundaries_in_cycles K 0) (cohomology_zero_cycle z) = z.
Proof.
have [v <-] := quotient_pi_surjective z.
by rewrite cohomology_zero_cycle_pi.
Qed.

Definition cohomology_zero_cycle_iso :
    @isomorphism (module_category R)
      [the lmodType R of cohomology K 0] [the lmodType R of cycle_module K 0].
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_of_linear cohomology_zero_cycle)
  (module_hom_of_linear (quotient_pi (boundaries_in_cycles K 0) :
    {linear cycle_module K 0 -> cohomology K 0})) _ _).
- apply module_hom_ext => z; exact: cohomology_zero_pi_cycle.
- apply module_hom_ext => z; exact: cohomology_zero_cycle_pi.
Defined.

End Zero.
End DiazParkHomologicalDegreeZero.
