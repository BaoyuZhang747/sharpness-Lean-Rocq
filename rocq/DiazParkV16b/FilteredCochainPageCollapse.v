(** Elementary consequences of the actual page homology quotient. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps HomologicalComplex HomologicalModuleIso.
From DiazParkV16b Require Import FilteredCochainCycles FilteredCochainPages FilteredCochainPageHomology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalModuleIso
  DPFilteredCycles DPFilteredPages DPFilteredPageHomology.
Local Open Scope ring_scope.

Module DPFilteredPageCollapse.
Section Collapse.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.

Lemma page_homology_zero_of_page_zero r p n (h : forall x : page F r p n, x=0)
    (x : page_homology F r p n) : x=0.
Proof.
have [z <-] := quotient_pi_surjective x.
have hz : z=0 by apply submodule_val_injective; exact: h.
by rewrite hz linear0.
Qed.

Variables (r : nat) (p : Z) (n : nat).
Hypothesis hd : forall x : page F r p n, page_d F r p n x=0.
Hypothesis hb : forall x : page F r p n, page_boundaries F r p n x -> x=0.

Lemma page_cycle_inclusion_kernel (x : page_homology_cycles F r p n) :
    page_homology_relations F r p n x <-> submodule_inclusion (linear_kernel (page_d F r p n)) x=0.
Proof.
split; [exact (@hb (submodule_val x))|].
intro hx; change (page_boundaries F r p n (submodule_val x)); change (submodule_val x=0) in hx.
rewrite hx; exact: subspace_zero.
Qed.

Lemma page_cycle_inclusion_surjective (x : page F r p n) :
    exists z : page_homology_cycles F r p n, submodule_inclusion (linear_kernel (page_d F r p n)) z=x.
Proof. exists (@submodule_in R (page F r p n) (linear_kernel (page_d F r p n)) x (hd x)); reflexivity. Qed.

Definition page_homology_zero_differentials_iso : @isomorphism (module_category R) (page_homology F r p n) (page F r p n) :=
  @quotient_linear_iso R (page_homology_cycles F r p n) (page F r p n)
    (page_homology_relations F r p n) (submodule_inclusion (linear_kernel (page_d F r p n)))
    page_cycle_inclusion_kernel page_cycle_inclusion_surjective.

Lemma page_homology_zero_differentials_iso_pi (z : page_homology_cycles F r p n) :
    module_hom_fun (iso_hom page_homology_zero_differentials_iso)
      (quotient_pi (page_homology_relations F r p n) z)=submodule_val z.
Proof.
change (@quotient_iso_map R (page_homology_cycles F r p n) (page F r p n)
  (page_homology_relations F r p n) (submodule_inclusion (linear_kernel (page_d F r p n)))
  page_cycle_inclusion_kernel (quotient_pi (page_homology_relations F r p n) z)=submodule_val z).
exact: quotient_iso_map_pi.
Qed.

End Collapse.
End DPFilteredPageCollapse.
