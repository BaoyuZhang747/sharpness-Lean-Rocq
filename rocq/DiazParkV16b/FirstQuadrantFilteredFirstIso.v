(** Genuine identification of the constructed filtered E1 page with native
    relative cohomology, proved by its exact representative kernel. *)
From Coq Require Import ZArith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps
  HomologicalComplex HomologicalCohomology HomologicalModuleIso.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalSupport FirstQuadrantCochainSpectralFiltration
  FirstQuadrantCochainSpectralRelative FirstQuadrantCochainSpectralFirst
  FilteredCochainCycles FilteredCochainPages FirstQuadrantFilteredPages FirstQuadrantFilteredFirstMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantSupport DPColumnFiltration
  DPColumnRelative DPColumnFirstPage DPFilteredCycles DPFilteredPages
  DPFirstQuadrantFilteredPages DPFirstQuadrantFilteredFirstMap.
Local Open Scope ring_scope.

Module DPFirstQuadrantFilteredFirstIso.
Section FirstIso.
Variable R : pzRingType.
Variable K : bicomplex R.
Let F := total_column_filtration K.

Lemma first_relative_boundary_iff p n (x : page_cycle_module F 0 (Z.of_nat p) n) :
    coboundary (relative_complex K p p.+1) n (first_cycle_relative x) <->
      page_relations F 0 (Z.of_nat p) n (submodule_val x).
Proof.
split.
- destruct n.
  + intro hx.
    change (quotient_pi (relative_subspace K p p.+1 0%N) (first_cycle_column K p 0%N x)=0) in hx.
    have hx' := proj1 (quotient_pi_kernel (relative_subspace K p p.+1 0%N) (first_cycle_column K p 0%N x)) hx.
    apply page_relations_next; apply (proj2 (@first_next_cycles R K p 0%N (submodule_val x))); exact hx'.
  + intros [v hv]; have [w hw] := quotient_pi_surjective v.
    change (@relative_d R K p p.+1 n v=first_cycle_relative x) in hv.
    rewrite -hw relative_d_pi in hv.
    have hd : column_subspace K p.+1 n.+1 (total_d (submodule_val w)-submodule_val x).
      apply/subspace_predP; move/eqP: hv; rewrite /first_cycle_relative quotient_pi_eq; exact (fun h => h).
    exists (submodule_val x-total_d (submodule_val w)),(total_d (submodule_val w)); split.
    * apply (proj2 (@first_next_cycles R K p n.+1 _)).
      have he : submodule_val x-total_d (submodule_val w) = -(total_d (submodule_val w)-submodule_val x) by rewrite opprB.
      rewrite he; exact: subspace_opp hd.
    * split; [|exact: subrK].
      split.
      -- apply (proj2 (@total_column_filtration_nat R K p n.+1 _)); exact: total_d_supported (submodule_val_mem w).
      -- exists (submodule_val w); split; [|reflexivity].
         change (filtration F (Z.sub (Z.of_nat p) 0) n (submodule_val w)).
         rewrite Z.sub_0_r; apply (proj2 (@total_column_filtration_nat R K p n _)); exact: submodule_val_mem.
- intros [a [b [ha [hb hab]]]].
  have ha' := proj1 (@first_next_cycles R K p n a) ha.
  destruct n.
  + have hb0 : b=0 := proj2 hb.
    change (quotient_pi (relative_subspace K p p.+1 0%N) (first_cycle_column K p 0%N x)=0).
    apply/(quotient_pi_kernel (relative_subspace K p p.+1 0%N) (first_cycle_column K p 0%N x)).
    change (column_subspace K p.+1 0%N (submodule_val x)).
    by rewrite -hab hb0 addr0.
  + destruct hb as [hb [v [hv hdv]]].
    have hv' : column_subspace K p n v.
      change (filtration F (Z.sub (Z.of_nat p) 0) n v) in hv.
      rewrite Z.sub_0_r in hv; exact (proj1 (@total_column_filtration_nat R K p n v) hv).
    exists (quotient_pi (relative_subspace K p p.+1 n) (@submodule_in R (total_term K n) (column_subspace K p n) v hv')).
    change (@relative_d R K p p.+1 n
      (quotient_pi (relative_subspace K p p.+1 n) (@submodule_in R (total_term K n) (column_subspace K p n) v hv')) = first_cycle_relative x).
    rewrite relative_d_pi; apply/eqP; rewrite /first_cycle_relative quotient_pi_eq; apply/subspace_predP.
    change (column_subspace K p.+1 n.+1 (total_d v-submodule_val x)).
    rewrite hdv.
    have he : b-submodule_val x = -a by rewrite -hab opprD addrCA subrr addr0.
    rewrite he; exact: subspace_opp ha'.
Qed.

Lemma first_cycle_native_kernel p n (x : page_cycle_module F 0 (Z.of_nat p) n) :
    page_denominator F 0 (Z.of_nat p) n x <-> first_cycle_native_class x=0.
Proof.
change (page_relations F 0 (Z.of_nat p) n (submodule_val x) <->
  cohomology_class (first_cycle_relative_cocycle x)=0).
rewrite cohomology_class_zero; symmetry; exact: first_relative_boundary_iff.
Qed.

Definition filtered_first_native_iso p n : @isomorphism (module_category R)
    (total_filtered_page K 0 (Z.of_nat p) n) (first_page K p n) :=
  @quotient_linear_iso R (page_cycle_module F 0 (Z.of_nat p) n) (first_page K p n)
    (page_denominator F 0 (Z.of_nat p) n) (@first_cycle_native_class R K p n)
    (@first_cycle_native_kernel p n) (@first_cycle_native_surjective R K p n).

Lemma filtered_first_native_iso_pi p n (x : page_cycle_module F 0 (Z.of_nat p) n) :
    module_hom_fun (iso_hom (filtered_first_native_iso p n))
      (quotient_pi (page_denominator F 0 (Z.of_nat p) n) x)=first_cycle_native_class x.
Proof.
change (@quotient_iso_map R (page_cycle_module F 0 (Z.of_nat p) n) (first_page K p n)
  (page_denominator F 0 (Z.of_nat p) n) (@first_cycle_native_class R K p n)
  (@first_cycle_native_kernel p n)
  (quotient_pi (page_denominator F 0 (Z.of_nat p) n) x)=first_cycle_native_class x).
exact: quotient_iso_map_pi.
Qed.

End FirstIso.
End DPFirstQuadrantFilteredFirstIso.
