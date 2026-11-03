(** Actual representatives of first-page classes obtained by inserting a
    vertical cocycle in a single column. *)
From Coq Require Import Arith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryModuleExactness ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps FirstQuadrantCochainTotalSupport FirstQuadrantCochainInclusion
  FirstQuadrantCochainSpectralFiltration FirstQuadrantCochainSpectralRelative
  FirstQuadrantCochainSpectralFirst FirstQuadrantCochainSpectralColumnTerms
  FirstQuadrantCochainSpectralColumn FirstQuadrantCochainSpectralColumnClasses
  CochainSignTwist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps
  DPFirstQuadrantSupport DPFirstQuadrantInclusion DPColumnFiltration DPColumnRelative
  DPColumnFirstPage DPColumnCoordinate DPColumnFirstIdentification DPColumnFirstClasses
  DPCochainSignTwist.
Local Open Scope ring_scope.

Module DPColumnFirstSeeds.
Section Seeds.
Variable R : pzRingType.
Variable K : bicomplex R.

Lemma first_seed_cocycle p q (z : cycle_module (vertical_complex K p) q) :
    cocycle (relative_complex K p p.+1) (q+p)%coq_nat
      (quotient_pi (relative_subspace K p p.+1 (q+p)%coq_nat)
        (column_coordinate_section (submodule_val z))).
Proof.
change (@relative_d R K p p.+1 (q+p)%coq_nat
  (quotient_pi (relative_subspace K p p.+1 (q+p)%coq_nat)
    (column_coordinate_section (submodule_val z))) = 0).
rewrite relative_d_pi.
apply/(quotient_pi_kernel (relative_subspace K p p.+1 (q+p).+1)
  (@column_d R K p (q+p)%coq_nat (column_coordinate_section (submodule_val z)))).
exact (@include_cycle_d_supported R K p q (q+p)%coq_nat (Nat.add_comm p q)
  (submodule_val z) (submodule_val_mem z)).
Qed.

Definition first_seed_cycle p q (z : cycle_module (vertical_complex K p) q) :
    cycle_module (relative_complex K p p.+1) (q+p)%coq_nat :=
  cycle_of_cocycle (first_seed_cocycle z).

Definition first_seed_class p q (z : cycle_module (vertical_complex K p) q) : first_page K p (q+p)%coq_nat :=
  quotient_pi (boundaries_in_cycles (relative_complex K p p.+1) (q+p)%coq_nat) (first_seed_cycle z).

Theorem first_seed_column_class p q (z : cycle_module (vertical_complex K p) q) :
    module_hom_fun (iso_hom (first_page_column_iso K p q)) (first_seed_class z) =
      (-1 : R)^+(p*q)%N *: quotient_pi (boundaries_in_cycles (vertical_complex K p) q) z.
Proof.
rewrite /first_seed_class first_page_column_iso_class -linearZ.
congr (quotient_pi _ _); apply submodule_val_injective.
rewrite first_page_vertical_cycle_val.
change ((-1 : R)^+(p*q)%N *:
  module_hom_fun (iso_hom (column_coordinate_iso K p q))
    (quotient_pi (relative_subspace K p p.+1 (q+p)%coq_nat)
      (column_coordinate_section (submodule_val z))) =
  (-1 : R)^+(p*q)%N *: submodule_val z).
by rewrite column_coordinate_iso_pi column_coordinate_section_spec.
Qed.

Theorem first_seed_class_surjective p q (x : first_page K p (q+p)%coq_nat) :
    exists z : cycle_module (vertical_complex K p) q, first_seed_class z = x.
Proof.
pose y := module_hom_fun (iso_hom (first_page_column_iso K p q)) x.
have [z hz] := quotient_pi_surjective ((-1 : R)^+(p*q)%N *: y).
exists z; apply (module_iso_hom_injective (e := first_page_column_iso K p q)).
rewrite first_seed_column_class hz.
change (sign_map (p*q)%N (sign_map (p*q)%N y) = y).
exact: sign_map_twice.
Qed.

End Seeds.
End DPColumnFirstSeeds.
