(** The first-page column comparison on actual cycle representatives. *)
From Coq Require Import Arith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryModuleExactness ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps CategoryComplexIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotalMaps
  FirstQuadrantCochainSpectralFiltration FirstQuadrantCochainSpectralRelative
  FirstQuadrantCochainSpectralFirst FirstQuadrantCochainSpectralColumnTerms
  FirstQuadrantCochainSpectralColumn CochainDegreeShift CochainSignTwist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DPFirstQuadrantCochain DPFirstQuadrantTotalMaps DPColumnFiltration DPColumnRelative
  DPColumnFirstPage DPColumnCoordinate DPColumnFirstIdentification
  DPCochainDegreeShift DPCochainSignTwist.
Local Open Scope ring_scope.

Module DPColumnFirstClasses.
Section Classes.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition first_page_vertical_cycle p q
    (z : cycle_module (relative_complex K p p.+1) (q+p)%coq_nat) :
    cycle_module (vertical_complex K p) q :=
  cycle_map (sign_twist_cochain_map (vertical_complex K p) p) q
    (cycle_map (graded_column_cochain_map K p) q z).

Theorem first_page_column_iso_class p q
    (z : cycle_module (relative_complex K p p.+1) (q+p)%coq_nat) :
    module_hom_fun (iso_hom (first_page_column_iso K p q))
      (quotient_pi (boundaries_in_cycles (relative_complex K p p.+1) (q+p)%coq_nat) z) =
    quotient_pi (boundaries_in_cycles (vertical_complex K p) q) (first_page_vertical_cycle z).
Proof.
pose e := degree_shift_cohomology_iso (@graded_column_below_zero R K p) q.
have he := @degree_shift_cohomology_iso_class R (relative_complex K p p.+1) p
  (@graded_column_below_zero R K p) q z.
have hi : module_hom_fun (iso_inv e)
    (quotient_pi (boundaries_in_cycles (relative_complex K p p.+1) (q+p)%coq_nat) z) =
    quotient_pi (boundaries_in_cycles (graded_column_shift K p) q) z.
  rewrite -he.
  exact: module_iso_hom_inv_apply.
change (cohomology_map (sign_twist_cochain_map (vertical_complex K p) p) q
  (cohomology_map (graded_column_cochain_map K p) q
    (module_hom_fun (iso_inv e)
      (quotient_pi (boundaries_in_cycles (relative_complex K p p.+1) (q+p)%coq_nat) z))) =
  quotient_pi (boundaries_in_cycles (vertical_complex K p) q) (first_page_vertical_cycle z)).
rewrite hi !cohomology_map_pi; reflexivity.
Qed.

Theorem first_page_vertical_cycle_val p q
    (z : cycle_module (relative_complex K p p.+1) (q+p)%coq_nat) :
    submodule_val (first_page_vertical_cycle z) =
      (-1 : R)^+(p*q)%N *: module_hom_fun (iso_hom (column_coordinate_iso K p q)) (submodule_val z).
Proof. reflexivity. Qed.

End Classes.
End DPColumnFirstClasses.
