(** The page-to-page law is proved from actual filtered cycles and boundaries.
    No exact-couple iteration, page homology, or convergence field is assumed. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps
  HomologicalComplex HomologicalModuleIso.
From DiazParkV16b Require Import FilteredCochainCycles FilteredCochainPages
  FilteredCochainPageHomology FilteredCochainPageCycleLifting
  FilteredCochainPageRepresentatives FilteredCochainPageKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalModuleIso
  DPFilteredCycles DPFilteredPages DPFilteredPageHomology DPFilteredPageCycleLifting
  DPFilteredPageRepresentatives DPFilteredPageKernel.
Local Open Scope ring_scope.

Module DPFilteredPageIteration.
Section Iteration.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.

Definition next_page_homology_iso r p n : @isomorphism (module_category R)
    (page F r.+1 p n) (page_homology F r p n) :=
  @quotient_linear_iso R (page_cycle_module F r.+1 p n) (page_homology F r p n)
    (page_denominator F r.+1 p n) (@next_cycle_to_homology R C F r p n)
    (@next_cycle_to_homology_kernel R C F r p n)
    (@next_cycle_to_homology_surjective R C F r p n).

Lemma next_page_homology_iso_pi r p n (x : page_cycle_module F r.+1 p n) :
    module_hom_fun (iso_hom (next_page_homology_iso r p n))
      (quotient_pi (page_denominator F r.+1 p n) x) = next_cycle_to_homology x.
Proof.
change (@quotient_iso_map R (page_cycle_module F r.+1 p n) (page_homology F r p n)
  (page_denominator F r.+1 p n) (@next_cycle_to_homology R C F r p n)
  (@next_cycle_to_homology_kernel R C F r p n)
  (quotient_pi (page_denominator F r.+1 p n) x)=next_cycle_to_homology x).
exact: quotient_iso_map_pi.
Qed.

End Iteration.
End DPFilteredPageIteration.
