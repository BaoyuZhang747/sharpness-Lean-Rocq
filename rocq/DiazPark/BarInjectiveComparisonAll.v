From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient HomologicalCohomology HomologicalDiagramLimits
  HomologicalModuleIso CategoryInjectiveResolution CategoryEnoughInjectives
  BarComplex BarDegreeZero BarInjectiveDegreeZero BarInjectiveComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkCohomology DiazParkHomologicalModuleIso DiazParkBarComplex
  DiazParkBarDegreeZero DiazParkBarInjectiveDegreeZero DiazParkBarInjectiveComparison.

Module DiazParkBarInjectiveComparisonAll.
Section AllDegrees.
Variable R : pzRingType.
Variable C : category.
Local Opaque module_quotient linear_preimage linear_kernel linear_image.

Definition bar_injective_cohomology_iso (D : module_codiagram R C)
    (J : injective_resolution D) n : @isomorphism (module_category R)
    [the lmodType R of cohomology (bar_complex D) n]
    [the lmodType R of cohomology (limit_complex (injective_resolution_complex J)) n].
Proof.
case: n => [|n].
- exact (module_iso_comp (bar_zero_cohomology_limit_iso D) (injective_degree_zero_iso J)).
- exact (bar_injective_positive_iso n J).
Defined.

(** Unconditional specialization: the resolution is constructed using the
    proved enough-injectives theorem for arbitrary modules and diagrams. *)
Definition bar_chosen_injective_cohomology_iso (D : module_codiagram R C) n :
    @isomorphism (module_category R)
      [the lmodType R of cohomology (bar_complex D) n]
      [the lmodType R of cohomology
        (limit_complex (injective_resolution_complex (chosen_injective_resolution R D))) n] :=
  bar_injective_cohomology_iso (chosen_injective_resolution R D) n.

End AllDegrees.
End DiazParkBarInjectiveComparisonAll.
