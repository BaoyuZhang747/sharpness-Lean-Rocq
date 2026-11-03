(** The genuine first page of the column filtration is isomorphic to ordinary
    vertical cohomology. Both the shift at degree zero and the total sign are
    handled by actual cochain/quotient maps. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalModuleIso CategoryComplexIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotalMaps
  FirstQuadrantCochainSpectralFiltration FirstQuadrantCochainSpectralRelative
  FirstQuadrantCochainSpectralFirst FirstQuadrantCochainSpectralColumnTerms
  CochainDegreeShift CochainSignTwist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DPFirstQuadrantCochain DPFirstQuadrantTotalMaps
  DPColumnFiltration DPColumnRelative DPColumnFirstPage DPColumnCoordinate
  DPCochainDegreeShift DPCochainSignTwist.
Local Open Scope ring_scope.

Module DPColumnFirstIdentification.
Section Identification.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition graded_column_shift p : cochain_complex R := degree_shift (relative_complex K p p.+1) p.

Definition graded_column_term_iso p q : @isomorphism (module_category R)
    (cochain_term (graded_column_shift p) q)
    (cochain_term (sign_twist (vertical_complex K p) p) q) := column_coordinate_iso K p q.

Lemma graded_column_term_commutes p q x :
    cochain_d (sign_twist (vertical_complex K p) p) q
      (module_hom_fun (iso_hom (graded_column_term_iso p q)) x) =
    module_hom_fun (iso_hom (graded_column_term_iso p q.+1))
      (cochain_d (graded_column_shift p) q x).
Proof.
have [v <-] := quotient_pi_surjective x.
change ((-1 : R)^+p *: vertical K p q
  (module_hom_fun (iso_hom (column_coordinate_iso K p q))
    (quotient_pi (relative_subspace K p p.+1 (q+p)%coq_nat) v)) =
  module_hom_fun (iso_hom (column_coordinate_iso K p q.+1))
    (@relative_d R K p p.+1 (q+p)%coq_nat (quotient_pi (relative_subspace K p p.+1 (q+p)%coq_nat) v))).
rewrite relative_d_pi !column_coordinate_iso_pi.
symmetry; exact: column_coordinate_d.
Qed.

Definition graded_column_cochain_map p := term_iso_cochain_map (@graded_column_term_commutes p).
Definition graded_column_cohomology_iso p q := term_iso_cohomology_iso (@graded_column_term_commutes p) q.

Lemma graded_column_below_zero p n (h : (n < p)%coq_nat)
    (x : cochain_term (relative_complex K p p.+1) n) : x = 0.
Proof.
have [v <-] := quotient_pi_surjective x.
have vz : v = 0 := column_beyond_degree_zero h v.
by rewrite vz linear0.
Qed.

Definition first_page_column_iso p q : @isomorphism (module_category R)
    (first_page K p (q+p)%coq_nat) (cohomology (vertical_complex K p) q) :=
  module_iso_comp
    (iso_symm (degree_shift_cohomology_iso (@graded_column_below_zero p) q))
    (module_iso_comp (graded_column_cohomology_iso p q)
      (sign_twist_cohomology_iso (vertical_complex K p) p q)).

End Identification.
End DPColumnFirstIdentification.
