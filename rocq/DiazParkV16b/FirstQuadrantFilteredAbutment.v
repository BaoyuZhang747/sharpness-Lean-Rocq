(** Collapse identifies actual total cohomology with E2's zero column via
    the canonical cocycle edge, not an arbitrary chosen isomorphism. *)
From Coq Require Import Arith ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps HomologicalComplex
  HomologicalCohomology HomologicalModuleIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FilteredCochainCycles FilteredCochainPages FilteredCochainCohomologyFiltration FilteredCochainFiniteConvergence
  FirstQuadrantFilteredPages FirstQuadrantFilteredCohomology FirstQuadrantFilteredConvergence
  FirstQuadrantFilteredCollapse FirstQuadrantFilteredGlobalCycles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPFilteredCycles DPFilteredPages
  DPFilteredCohomologyFiltration DPFilteredFiniteConvergence DPFirstQuadrantFilteredPages
  DPFirstQuadrantFilteredCohomology DPFirstQuadrantFilteredConvergence DPFirstQuadrantFilteredCollapse
  DPFirstQuadrantFilteredGlobalCycles.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredAbutment.
Section Abutment.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.
Variable h2 : forall p n (x : page F 1 (Z.of_nat p.+1) n), x=0.

Lemma positive_associated_graded_zero p n (x : associated_graded F (Z.of_nat p.+1) n) : x=0.
Proof.
have h : Nat.le (Nat.add (Nat.add n (S p)) 1) (S (Nat.add n (S p))) by lia.
pose e := @total_stable_page_iso R K (S (Nat.add n (S p))) (S p) n h.
have hx : module_hom_fun (iso_inv e) x=0 := later_positive_zero h2 (module_hom_fun (iso_inv e) x).
have he := congr1 (module_hom_fun (iso_hom e)) hx.
by rewrite module_iso_inv_hom_apply module_hom_zero in he.
Qed.

Lemma positive_cohomology_filtration_step p n x : total_cohomology_filtration K p.+1 n x ->
    total_cohomology_filtration K p.+2 n x.
Proof.
intro hx.
pose z := @submodule_in R (cohomology (total_complex K) n) (cohomology_filtration F (Z.of_nat p.+1) n) x hx.
have hz := @positive_associated_graded_zero p n
  (quotient_pi (linear_preimage (submodule_inclusion (cohomology_filtration F (Z.of_nat p.+1) n))
    (cohomology_filtration F (Z.succ (Z.of_nat p.+1)) n)) z).
have hm := proj1 (quotient_pi_kernel _ z) hz.
change (cohomology_filtration F (Z.succ (Z.of_nat p.+1)) n x) in hm.
change (cohomology_filtration F (Z.of_nat p.+2) n x).
by rewrite Nat2Z.inj_succ.
Qed.

Theorem positive_cohomology_filtration_zero p n x : total_cohomology_filtration K p.+1 n x -> x=0.
Proof.
have haux : forall k p, Nat.lt n (Nat.add (S p) k) -> forall x, total_cohomology_filtration K p.+1 n x -> x=0.
  intro k; induction k as [|k ih]; intros a ha y hy.
  - apply: (@total_cohomology_filtration_bounded R K a.+1 n _ y hy); lia.
  - apply: (ih a.+1 _ y (positive_cohomology_filtration_step hy)); lia.
intro hx; apply: (haux n.+1 p _ x hx); lia.
Qed.

Lemma zero_graded_inclusion_kernel n (x : submodule_carrier (cohomology_filtration F 0 n)) :
    linear_preimage (submodule_inclusion (cohomology_filtration F 0 n)) (cohomology_filtration F 1 n) x <->
      submodule_inclusion (cohomology_filtration F 0 n) x=0.
Proof.
split.
- exact (@positive_cohomology_filtration_zero 0 n (submodule_val x)).
- intro hx; change (cohomology_filtration F 1 n (submodule_val x)); change (submodule_val x=0) in hx.
  rewrite hx; exact: subspace_zero.
Qed.

Lemma zero_graded_inclusion_surjective n (x : cohomology (total_complex K) n) :
    exists z : submodule_carrier (cohomology_filtration F 0 n), submodule_inclusion (cohomology_filtration F 0 n) z=x.
Proof.
exists (@submodule_in R (cohomology (total_complex K) n) (cohomology_filtration F 0 n) x
  (total_cohomology_filtration_zero_full x)); reflexivity.
Qed.

Definition zero_graded_total_iso n : @isomorphism (module_category R) (associated_graded F 0 n) (cohomology (total_complex K) n) :=
  @quotient_linear_iso R (submodule_carrier (cohomology_filtration F 0 n)) (cohomology (total_complex K) n)
    (linear_preimage (submodule_inclusion (cohomology_filtration F 0 n)) (cohomology_filtration F 1 n))
    (submodule_inclusion (cohomology_filtration F 0 n)) (@zero_graded_inclusion_kernel n) (@zero_graded_inclusion_surjective n).

Lemma zero_graded_total_iso_pi n (z : submodule_carrier (cohomology_filtration F 0 n)) :
    module_hom_fun (iso_hom (zero_graded_total_iso n))
      (quotient_pi (linear_preimage (submodule_inclusion (cohomology_filtration F 0 n)) (cohomology_filtration F 1 n)) z)=submodule_val z.
Proof.
change (@quotient_iso_map R (submodule_carrier (cohomology_filtration F 0 n)) (cohomology (total_complex K) n)
  (linear_preimage (submodule_inclusion (cohomology_filtration F 0 n)) (cohomology_filtration F 1 n))
  (submodule_inclusion (cohomology_filtration F 0 n)) (@zero_graded_inclusion_kernel n)
  (quotient_pi (linear_preimage (submodule_inclusion (cohomology_filtration F 0 n)) (cohomology_filtration F 1 n)) z)=submodule_val z).
exact: quotient_iso_map_pi.
Qed.

Definition zero_stable_bound (n : nat) : Nat.le (Nat.add (Nat.add n 0) 1) (S n).
Proof. lia. Qed.

Definition zero_stable_total_iso n : @isomorphism (module_category R) (page F n.+1 0 n) (cohomology (total_complex K) n) :=
  module_iso_comp (total_stable_page_iso K (zero_stable_bound n)) (zero_graded_total_iso n).

Lemma zero_stable_total_global_cycle n (z : cycle_module (total_complex K) n) :
    module_hom_fun (iso_hom (zero_stable_total_iso n)) (@global_cycle_page R K n.+1 n z)=
      quotient_pi (boundaries_in_cycles (total_complex K) n) z.
Proof.
change (module_hom_fun (iso_hom (zero_graded_total_iso n))
  (module_hom_fun (iso_hom (total_stable_page_iso K (zero_stable_bound n))) (@global_cycle_page R K n.+1 n z)) =
    quotient_pi (boundaries_in_cycles (total_complex K) n) z).
rewrite /global_cycle_page total_stable_page_iso_pi /stable_page_class /filtered_cocycle_graded zero_graded_total_iso_pi.
change (@filtered_cocycle_class R (total_complex K) F 0 n
  (@stable_cycle_map R (total_complex K) F
    (fun t m x ht hx => @total_column_filtration_bounded R K t m ht x hx)
    n.+1 0 n (total_stable_high (zero_stable_bound n)) (global_cycle_to_filtered K n.+1 n z)) =
  quotient_pi (boundaries_in_cycles (total_complex K) n) z).
unfold filtered_cocycle_class.
f_equal; apply submodule_val_injective; reflexivity.
Qed.

Lemma zero_stable_total_inverse n (x : cohomology (total_complex K) n) :
    module_hom_fun (iso_inv (zero_stable_total_iso n)) x=total_to_zero_page K n.+1 n x.
Proof.
apply (module_iso_hom_injective (e:=zero_stable_total_iso n)); rewrite module_iso_inv_hom_apply.
have [z <-] := quotient_pi_surjective x.
rewrite total_to_zero_page_pi zero_stable_total_global_cycle; reflexivity.
Qed.

Definition total_zero_second_iso n : @isomorphism (module_category R) (cohomology (total_complex K) n) (page F 1 0 n) :=
  module_iso_comp (iso_symm (zero_stable_total_iso n)) (zero_column_back_iso h2 n n).

Theorem total_zero_second_iso_edge n (x : cohomology (total_complex K) n) :
    module_hom_fun (iso_hom (total_zero_second_iso n)) x=total_to_zero_page K 1 n x.
Proof.
change (module_hom_fun (iso_hom (zero_column_back_iso h2 n n))
  (module_hom_fun (iso_inv (zero_stable_total_iso n)) x)=total_to_zero_page K 1 n x).
rewrite zero_stable_total_inverse; exact: zero_column_back_total.
Qed.

End Abutment.
End DPFirstQuadrantFilteredAbutment.
