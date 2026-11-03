(** Reindexing the actual native first-page row by p+q, with explicit
    equality transport to the previously proved q+p convention. *)
From Coq Require Import Arith ZArith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso CategoryComplexIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainSpectralRelative
  FirstQuadrantCochainSpectralFirst FirstQuadrantCochainSpectralD1 FirstQuadrantCochainSpectralSecond
  CochainDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalModuleIso
  DPFirstQuadrantCochain DPColumnRelative DPColumnFirstPage DPColumnD1 DPColumnSecondPage DPCochainDegreeTransport.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredSecondRow.
Section Transport.
Variable R : pzRingType.
Variable C : cochain_complex R.
Lemma cohomology_degree_iso_comp n m k (h:n=m) (h':m=k) x :
    module_hom_fun (iso_hom (@cohomology_degree_iso R C m k h'))
      (module_hom_fun (iso_hom (@cohomology_degree_iso R C n m h)) x) =
    module_hom_fun (iso_hom (@cohomology_degree_iso R C n k (Logic.eq_trans h h'))) x.
Proof. destruct h; destruct h'; reflexivity. Qed.
End Transport.
Section Row.
Variable R : pzRingType.
Variable K : bicomplex R.

Definition first_page_row_swapped q : cochain_complex R :=
  @CochainComplex R (fun p => first_page K p (p+q)%coq_nat)
    (fun p => (@first_d R K p (p+q)%coq_nat : {linear _ -> _}))
    (fun p x => @first_d_squared R K p (p+q)%coq_nat x).

Lemma first_d_degree_iso p n m (h:n=m) (x:first_page K p n) :
    first_d (module_hom_fun (iso_hom (@cohomology_degree_iso R (relative_complex K p p.+1) n m h)) x) =
    module_hom_fun (iso_hom (@cohomology_degree_iso R (relative_complex K p.+1 p.+2) n.+1 m.+1
      (f_equal S h))) (first_d x).
Proof. destruct h; reflexivity. Qed.

Definition first_row_swapped_term_iso q p : @isomorphism (module_category R)
    (cochain_term (first_page_row_swapped q) p) (cochain_term (first_page_row K q) p) :=
  @cohomology_degree_iso R (relative_complex K p p.+1) (p+q)%coq_nat (q+p)%coq_nat (Nat.add_comm p q).

Lemma first_row_swapped_commutes q p x :
    cochain_d (first_page_row K q) p (module_hom_fun (iso_hom (first_row_swapped_term_iso q p)) x) =
    module_hom_fun (iso_hom (first_row_swapped_term_iso q p.+1)) (cochain_d (first_page_row_swapped q) p x).
Proof.
change (first_d_row (module_hom_fun (iso_hom (first_row_swapped_term_iso q p)) x) =
  module_hom_fun (iso_hom (first_row_swapped_term_iso q p.+1)) (first_d x)).
rewrite /first_d_row /first_row_swapped_term_iso first_d_degree_iso cohomology_degree_iso_comp.
have he : Logic.eq_trans (f_equal S (Nat.add_comm p q)) (row_degree p q)=Nat.add_comm p.+1 q by apply Prop_irrelevance.
rewrite he; reflexivity.
Qed.

Definition first_row_swapped_cohomology_iso q p : @isomorphism (module_category R)
    (cohomology (first_page_row_swapped q) p) (second_page K p q) :=
  term_iso_cohomology_iso (@first_row_swapped_commutes q) p.

End Row.
End DPFirstQuadrantFilteredSecondRow.
