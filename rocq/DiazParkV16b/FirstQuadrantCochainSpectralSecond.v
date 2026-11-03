(** The actual second page is native cohomology of the constructed first-page
    row and actual d1. Its comparison with horizontal cohomology of vertical
    cohomology is derived from the proved first-differential comparison. *)
From Coq Require Import Arith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso CategoryComplexIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotalMaps
  FirstQuadrantCochainEdge FirstQuadrantCochainSpectralFirst FirstQuadrantCochainSpectralColumn
  FirstQuadrantCochainSpectralD1 CochainSignTwist.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DPFirstQuadrantCochain DPFirstQuadrantTotalMaps
  DPFirstQuadrantEdge DPColumnFirstPage DPColumnFirstIdentification DPColumnD1 DPCochainSignTwist.
Local Open Scope ring_scope.

Module DPColumnSecondPage.
Section Second.
Variable R : pzRingType.
Variable K : bicomplex R.

Lemma horizontal_cohomology_squared p q (x : cohomology (vertical_complex K p) q) :
    horizontal_cohomology K p.+1 q (horizontal_cohomology K p q x) = 0.
Proof.
have [z <-] := quotient_pi_surjective x.
rewrite /horizontal_cohomology !cohomology_map_pi.
have hz : cycle_map (horizontal_column_map K p.+1) q
    (cycle_map (horizontal_column_map K p) q z) = 0.
  apply submodule_val_injective.
  change (horizontal K p.+1 q (horizontal K p q (submodule_val z)) = 0).
  exact: horizontal_squared.
by rewrite hz linear0.
Qed.

Definition horizontal_cohomology_row q : cochain_complex R :=
  @CochainComplex R (fun p => cohomology (vertical_complex K p) q)
    (fun p => horizontal_cohomology K p q) (fun p x => horizontal_cohomology_squared x).

Lemma first_d_row_squared p q (x : first_page K p (q+p)%coq_nat) :
    first_d_row (first_d_row x) = 0.
Proof.
apply (module_iso_hom_injective (e := first_page_column_iso K p.+2 q)).
rewrite module_hom_zero !first_d_row_column linearZ.
change ((-1 : R)^+q *: ((-1 : R)^+q *:
  horizontal_cohomology K p.+1 q
    (horizontal_cohomology K p q (module_hom_fun (iso_hom (first_page_column_iso K p q)) x))) = 0).
by rewrite horizontal_cohomology_squared !scaler0.
Qed.

Definition first_page_row q : cochain_complex R :=
  @CochainComplex R (fun p => first_page K p (q+p)%coq_nat)
    (fun p => (@first_d_row R K p q : {linear _ -> _}))
    (fun p x => @first_d_row_squared p q x).

Definition first_page_row_term_iso q p : @isomorphism (module_category R)
    (cochain_term (first_page_row q) p)
    (cochain_term (sign_twist (horizontal_cohomology_row q) q) p) :=
  first_page_column_iso K p q.

Lemma first_page_row_term_commutes q p x :
    cochain_d (sign_twist (horizontal_cohomology_row q) q) p
      (module_hom_fun (iso_hom (first_page_row_term_iso q p)) x) =
    module_hom_fun (iso_hom (first_page_row_term_iso q p.+1))
      (cochain_d (first_page_row q) p x).
Proof. symmetry; exact: first_d_row_column. Qed.

Definition first_page_row_cochain_map q := term_iso_cochain_map (@first_page_row_term_commutes q).

Definition second_page p q : lmodType R := cohomology (first_page_row q) p.

Definition second_page_horizontal_iso p q : @isomorphism (module_category R)
    (second_page p q) (cohomology (horizontal_cohomology_row q) p) :=
  module_iso_comp (term_iso_cohomology_iso (@first_page_row_term_commutes q) p)
    (sign_twist_cohomology_iso (horizontal_cohomology_row q) q p).

End Second.
End DPColumnSecondPage.
