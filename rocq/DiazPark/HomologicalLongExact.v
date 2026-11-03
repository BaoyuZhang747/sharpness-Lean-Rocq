(** The full long exact cohomology sequence of an actual degreewise short
    exact sequence: all three positions in every degree and the initial mono. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalConnecting HomologicalShortExactMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalConnecting.
Local Open Scope ring_scope.

Section LongExact.
Variable R : pzRingType.
Variables A B C : @cochain_complex R.
Variables (f : cochain_map A B) (g : cochain_map B C).
Variable s : degreewise_short_exact f g.

Theorem connecting_map_image n (q : cohomology A n.+1) :
  cohomology_map f n.+1 q = 0 <->
    exists r : cohomology C n, connecting_map s n r = q.
Proof.
split.
- move=> hq; have [a ha] := quotient_pi_surjective q.
  rewrite -ha cohomology_map_pi in hq; rewrite -ha.
  have hf : coboundary B n.+1 (cochain_map_at f n.+1 (cycle_inclusion A n.+1 a)).
    apply/boundary_subspaceE.
    have hm : boundaries_in_cycles B n.+1 (cycle_map f n.+1 a).
      apply/quotient_pi_kernel; exact: hq.
    exact: hm.
  have [b hb] := hf.
  have hz : cocycle C n (cochain_map_at g n b).
    rewrite /cocycle cochain_map_commutes hb.
    exact: (@short_exact_composite R A B C f g s n.+1).
  exists (cohomology_class hz).
  rewrite /cohomology_class connecting_map_pi.
  apply: (@connecting_class_solution R A B C f g s n (cycle_of_cocycle hz) b a).
  + reflexivity.
  + exact: esym hb.
- move=> [r <-]; have [z <-] := quotient_pi_surjective r.
  rewrite connecting_map_pi /connecting_class cohomology_map_pi.
  apply/quotient_pi_kernel; apply/boundary_subspaceE.
  change (exists b, cochain_d B n b =
    cochain_map_at f n.+1 (connecting_preimage s z)).
  exists (connecting_lift s z); symmetry; exact: connecting_preimage_spec.
Qed.

Lemma cohomology_inclusion_zero_kernel (q : cohomology A 0) :
  cohomology_map f 0 q = 0 -> q = 0.
Proof.
move=> hq; have [a ha] := quotient_pi_surjective q.
rewrite -ha cohomology_map_pi in hq; rewrite -ha.
have hf : cochain_map_at f 0 (cycle_inclusion A 0 a) = 0.
  have hm : boundaries_in_cycles B 0 (cycle_map f 0 a).
    apply/quotient_pi_kernel; exact: hq.
  exact: hm.
have az : a = 0.
  apply submodule_val_injective.
  apply: (@short_exact_injective R A B C f g s 0).
  rewrite linear0; exact: hf.
rewrite az; exact: linear0.
Qed.

Theorem cohomology_inclusion_zero_injective : injective (cohomology_map f 0).
Proof.
move=> x y hxy.
have hz : cohomology_map f 0 (x-y) = 0 by rewrite linearB hxy subrr.
exact: subr0_eq (cohomology_inclusion_zero_kernel hz).
Qed.

Theorem long_exact_cohomology :
  injective (cohomology_map f 0) /\
  forall n,
    linear_exact (cohomology_map f n) (cohomology_map g n) /\
    linear_exact (cohomology_map g n) (connecting_map s n) /\
    linear_exact (connecting_map s n) (cohomology_map f n.+1).
Proof.
split; first exact: cohomology_inclusion_zero_injective.
move=> n; split; first exact: cohomology_middle_exact.
split; [exact: connecting_map_kernel | exact: connecting_map_image].
Qed.

End LongExact.
