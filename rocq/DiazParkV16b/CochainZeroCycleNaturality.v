(** Naturality of the actual H0-to-cycles identification. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalDegreeZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalDegreeZero.

Module DPCochainZeroCycleNaturality.
Lemma cohomology_zero_cycle_map {R : pzRingType} {K L : cochain_complex R} (f : cochain_map K L)
    (x : cohomology K 0) :
    cohomology_zero_cycle L (cohomology_map f 0 x)=cycle_map f 0 (cohomology_zero_cycle K x).
Proof. have [z <-] := quotient_pi_surjective x; by rewrite cohomology_map_pi !cohomology_zero_cycle_pi. Qed.

Lemma cohomology_zero_cycle_map_val {R : pzRingType} {K L : cochain_complex R} (f : cochain_map K L)
    (x : cohomology K 0) :
    submodule_val (cohomology_zero_cycle L (cohomology_map f 0 x))=
      cochain_map_at f 0 (submodule_val (cohomology_zero_cycle K x)).
Proof. rewrite cohomology_zero_cycle_map; reflexivity. Qed.
End DPCochainZeroCycleNaturality.
