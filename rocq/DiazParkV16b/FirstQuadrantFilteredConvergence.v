(** Finite convergence of the actual column spectral sequence to actual total
    cohomology, with an explicit page bound and the literal image filtration. *)
From Coq Require Import Arith ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex
  HomologicalCohomology HomologicalModuleIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FilteredCochainCycles FilteredCochainPages FilteredCochainCohomologyFiltration
  FilteredCochainFiniteConvergence FirstQuadrantFilteredPages FirstQuadrantFilteredCohomology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPFilteredCycles DPFilteredPages
  DPFilteredCohomologyFiltration DPFilteredFiniteConvergence DPFirstQuadrantFilteredPages DPFirstQuadrantFilteredCohomology.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredConvergence.
Section Convergence.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Definition total_stable_high r p n (h : (n+p+1<=r)%coq_nat) :
    Z.lt (Z.of_nat n.+1) (Z.add (Z.of_nat p) (Z.of_nat r.+1)).
Proof.
have hz := proj1 (Nat2Z.inj_le (n+p+1)%coq_nat r) h.
rewrite !Nat2Z.inj_add in hz; rewrite !Nat2Z.inj_succ; lia.
Qed.
Definition total_stable_low r p n (h : (n+p+1<=r)%coq_nat) :
    Z.le (Z.sub (Z.of_nat p) (Z.of_nat r)) 0.
Proof.
have hz := proj1 (Nat2Z.inj_le (n+p+1)%coq_nat r) h.
rewrite !Nat2Z.inj_add in hz; lia.
Qed.

Definition total_stable_page_iso r p n (h : (n+p+1<=r)%coq_nat) : @isomorphism (module_category R)
    (total_filtered_page K r (Z.of_nat p) n) (associated_graded F (Z.of_nat p) n) :=
  @stable_page_associated_graded_iso R (total_complex K) F
    (fun t m x ht => @total_column_filtration_nonpositive R K t m ht x)
    (fun t m x ht hx => @total_column_filtration_bounded R K t m ht x hx)
    r (Z.of_nat p) n (total_stable_high h) (total_stable_low h).

Lemma total_stable_page_iso_pi r p n (h : (n+p+1<=r)%coq_nat)
    (x : page_cycle_module F r (Z.of_nat p) n) :
    module_hom_fun (iso_hom (total_stable_page_iso h)) (quotient_pi (page_denominator F r (Z.of_nat p) n) x) =
      @stable_page_class R (total_complex K) F
        (fun t m x ht hx => @total_column_filtration_bounded R K t m ht x hx)
        r (Z.of_nat p) n (total_stable_high h) x.
Proof. exact: stable_page_associated_graded_iso_pi. Qed.

Theorem total_filtered_d_stable_zero r p n (h : Z.lt (Z.of_nat n.+1) (Z.add p (Z.of_nat r.+1)))
    (x : total_filtered_page K r p n) : total_filtered_d K r p n x=0.
Proof.
have [z <-] := quotient_pi_surjective x.
change (page_d F r p n (quotient_pi (page_denominator F r p n) z)=0).
rewrite page_d_pi.
have hd : total_d (submodule_val z)=0.
  exact (@total_column_filtration_bounded R K (Z.add p (Z.of_nat r.+1)) n.+1 h _ (proj2 (submodule_val_mem z))).
have hz : page_cycle_d F r p n z=0 by apply submodule_val_injective; exact hd.
by rewrite hz linear0.
Qed.

Definition total_finite_convergence_iso p n : @isomorphism (module_category R)
    (total_filtered_page K (n+p+1)%coq_nat (Z.of_nat p) n) (associated_graded F (Z.of_nat p) n) :=
  total_stable_page_iso (Nat.le_refl (n+p+1)%coq_nat).

End Convergence.
End DPFirstQuadrantFilteredConvergence.
