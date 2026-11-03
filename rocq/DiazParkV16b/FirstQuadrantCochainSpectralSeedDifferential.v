(** The native connecting homomorphism, and therefore d1, on actual
    one-column vertical-cocycle representatives. *)
From Coq Require Import Arith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalConnecting.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps FirstQuadrantCochainTotalSupport FirstQuadrantCochainLeading
  FirstQuadrantCochainInclusion FirstQuadrantCochainSpectralFiltration
  FirstQuadrantCochainSpectralRelative FirstQuadrantCochainSpectralFirst
  FirstQuadrantCochainSpectralColumnTerms FirstQuadrantCochainSpectralSeeds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalConnecting DPFirstQuadrantCochain DPFirstQuadrantTotal
  DPFirstQuadrantTotalMaps DPFirstQuadrantSupport DPFirstQuadrantLeading DPFirstQuadrantInclusion
  DPColumnFiltration DPColumnRelative DPColumnFirstPage DPColumnCoordinate DPColumnFirstSeeds.
Local Open Scope ring_scope.

Module DPColumnSeedDifferential.
Section SeedDifferential.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition seed_d_term p q (z : cycle_module (vertical_complex K p) q) :
    column_term K p.+1 (q+p).+1 :=
  @submodule_in R (total_term K (q+p).+1) (column_subspace K p.+1 (q+p).+1)
    (total_d (total_include (Nat.add_comm p q) (submodule_val z)))
    (include_cycle_d_supported (Nat.add_comm p q) (submodule_val_mem z)).

Lemma seed_d_cocycle p q (z : cycle_module (vertical_complex K p) q) :
    cocycle (column_complex K p.+1) (q+p).+1 (seed_d_term z).
Proof.
apply submodule_val_injective.
change (total_d (total_d (total_include (Nat.add_comm p q) (submodule_val z))) = 0).
exact: total_d_squared.
Qed.

Definition seed_d_cycle p q (z : cycle_module (vertical_complex K p) q) :
    cycle_module (column_complex K p.+1) (q+p).+1 := cycle_of_cocycle (seed_d_cocycle z).

Theorem couple_k_seed p q (z : cycle_module (vertical_complex K p) q) :
    couple_k K p (q+p)%coq_nat (first_seed_class z) =
      quotient_pi (boundaries_in_cycles (column_complex K p.+1) (q+p).+1) (seed_d_cycle z).
Proof.
change (connecting_map (relative_short_exact K (filtration_succ p)) (q+p)%coq_nat
  (quotient_pi (boundaries_in_cycles (relative_complex K p p.+1) (q+p)%coq_nat)
    (first_seed_cycle z)) =
  quotient_pi (boundaries_in_cycles (column_complex K p.+1) (q+p).+1) (seed_d_cycle z)).
rewrite connecting_map_pi.
apply: (@connecting_class_solution R (column_complex K p.+1) (column_complex K p)
  (relative_complex K p p.+1) (column_transition K (filtration_succ p))
  (relative_projection K p p.+1) (relative_short_exact K (filtration_succ p))
  (q+p)%coq_nat (first_seed_cycle z) (column_coordinate_section (submodule_val z))
  (seed_d_cycle z)).
- reflexivity.
- apply submodule_val_injective; reflexivity.
Qed.

Theorem first_d_seed p q (z : cycle_module (vertical_complex K p) q) :
    first_d (first_seed_class z) =
      quotient_pi (boundaries_in_cycles (relative_complex K p.+1 p.+2) (q+p).+1)
        (cycle_map (relative_projection K p.+1 p.+2) (q+p).+1 (seed_d_cycle z)).
Proof.
change (cohomology_map (relative_projection K p.+1 p.+2) (q+p).+1
  (couple_k K p (q+p)%coq_nat (first_seed_class z)) =
  quotient_pi (boundaries_in_cycles (relative_complex K p.+1 p.+2) (q+p).+1)
    (cycle_map (relative_projection K p.+1 p.+2) (q+p).+1 (seed_d_cycle z))).
by rewrite couple_k_seed cohomology_map_pi.
Qed.

Theorem seed_d_horizontal_coordinate p q (z : cycle_module (vertical_complex K p) q) :
    submodule_val (seed_d_term z) p.+1 q (horizontal_output_index (Nat.add_comm p q)) =
      horizontal K p q (submodule_val z).
Proof. exact: include_d_horizontal. Qed.

End SeedDifferential.
End DPColumnSeedDifferential.
