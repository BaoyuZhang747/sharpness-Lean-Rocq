(** Injectivity of the actual zero-column edge by finite elimination. *)
From Coq Require Import Arith Lia.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import HomologicalComplex HomologicalMaps HomologicalCohomology
  HomologicalCohomologyMaps ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import FirstQuadrantCochainBicomplex FirstQuadrantCochainTotal
  FirstQuadrantCochainTotalMaps FirstQuadrantCochainTotalSupport FirstQuadrantCochainEdge
  FirstQuadrantCochainLeading FirstQuadrantCochainInclusion FirstQuadrantCochainElimination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology
  DiazParkCohomologyMaps DPFirstQuadrantCochain DPFirstQuadrantTotal DPFirstQuadrantTotalMaps
  DPFirstQuadrantSupport DPFirstQuadrantEdge DPFirstQuadrantLeading DPFirstQuadrantInclusion
  DPFirstQuadrantElimination.
Local Open Scope ring_scope.

Module DPFirstQuadrantEdgeInjective.
Section Injectivity.
Variable R : pzRingType.
Variable K : bicomplex R.
Variable hK : positive_horizontal_exact K.

Lemma zero_column_boundary_total_boundary n (x : total_term K n)
    (hx : cocycle (total_complex K) n x)
    (hz : coboundary (vertical_complex K 0%N) n (zero_column_at x)) :
    coboundary (total_complex K) n x.
Proof.
destruct n as [|n].
- change (x = 0).
  apply functional_extensionality_dep; intro p.
  apply functional_extensionality_dep; intro q.
  apply functional_extensionality_dep; intro h.
  have ep : p = 0%N by lia. have eq : q = 0%N by lia.
  subst p; subst q.
  have eh : h = Logic.eq_refl by apply Prop_irrelevance.
  rewrite eh. exact hz.
- destruct hz as [b hb].
  pose y0 : total_term K n := total_include (Logic.eq_refl : (0 + n)%coq_nat = n) b.
  have hs : supported_from (x - total_d y0) 1%N.
    intros p q h hp.
    have ep : p = 0%N by lia. subst p.
    have eq : q = n.+1 by lia. subst q.
    change (x 0%N n.+1 h - @total_d R K n y0 0%N n.+1 h = 0).
    have eh : h = vertical_output_index (Logic.eq_refl : (0 + n)%coq_nat = n)
      by apply Prop_irrelevance.
    rewrite eh /y0 include_d_vertical expr0 scale1r.
    change (vertical K 0%N n b = x 0%N n.+1 Logic.eq_refl) in hb.
    have ez : vertical_output_index (Logic.eq_refl : (0 + n)%coq_nat = n) = Logic.eq_refl
      by apply Prop_irrelevance.
    by rewrite ez hb subrr.
  have [y [hy _]] := @tail_cycle_boundary R K hK n 0%N (x - total_d y0)
    (corrected_cocycle y0 hx) hs.
  exists (y0 + y).
  change (total_d (y0 + y) = x).
  rewrite linearD.
  change (total_d y0 + total_d y = x).
  by rewrite hy addrC subrK.
Qed.

Lemma edge_map_kernel_zero n (x : cohomology (total_complex K) n) :
    edge_map K n x = 0 -> x = 0.
Proof.
intro hx.
have he := f_equal (@submodule_val R (cohomology (vertical_complex K 0%N) n) (edge_kernel K n)) hx.
change (cohomology_map (zero_column_projection K) n x = 0) in he.
have [z hz] := quotient_pi_surjective x.
rewrite <- hz in he.
rewrite cohomology_map_pi in he.
have hb : coboundary (vertical_complex K 0%N) n
    (zero_column_at (cycle_inclusion (total_complex K) n z)).
  apply/boundary_subspaceE.
  exact (proj1 (quotient_pi_kernel (boundaries_in_cycles (vertical_complex K 0%N) n)
    (cycle_map (zero_column_projection K) n z)) he).
rewrite <- hz; apply/quotient_pi_kernel; apply/boundary_subspaceE.
exact (@zero_column_boundary_total_boundary n
  (cycle_inclusion (total_complex K) n z) (submodule_val_mem z) hb).
Qed.

Theorem edge_map_injective n : injective (edge_map K n).
Proof.
intros x y h.
have hz : edge_map K n (x - y) = 0 by rewrite linearB h subrr.
exact (subr0_eq (edge_map_kernel_zero hz)).
Qed.
End Injectivity.
End DPFirstQuadrantEdgeInjective.
