From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalConnecting HomologicalModuleIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalConnecting DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

(** Exactness on the actual cohomology quotients, with no degree-zero
    vanishing implicit in the positive-degree consequences. *)
Section ShortExactMaps.
Variable R : pzRingType.
Variables A B C : @cochain_complex R.
Variables (f : cochain_map A B) (g : cochain_map B C).
Variable s : degreewise_short_exact f g.

Lemma cohomology_middle_cycle n (b : cycle_module B n)
    (hb : cochain_map_at g n (cycle_inclusion B n b) = 0) :
  exists a : cohomology A n,
    cohomology_map f n a = quotient_pi (boundaries_in_cycles B n) b.
Proof.
have [a ha] := @short_exact_kernel R A B C f g s n _ hb.
have ac : cocycle A n a.
  apply: (@short_exact_injective R A B C f g s n.+1).
  rewrite linear0 -cochain_map_commutes ha.
  exact: (submodule_val_mem b).
exists (cohomology_class ac); rewrite cohomology_map_class /cohomology_class.
congr (quotient_pi _ _); apply submodule_val_injective; exact: ha.
Qed.

Theorem cohomology_middle_exact n (q : cohomology B n) :
  cohomology_map g n q = 0 <->
    exists a : cohomology A n, cohomology_map f n a = q.
Proof.
split.
- move=> hq; have [b hb] := quotient_pi_surjective q.
  rewrite -hb cohomology_map_pi in hq; rewrite -hb.
  have gb : coboundary C n
      (cochain_map_at g n (cycle_inclusion B n b)).
    apply/boundary_subspaceE.
    have hm : boundaries_in_cycles C n (cycle_map g n b).
      apply/quotient_pi_kernel; exact: hq.
    exact: hm.
  clear q hb.
  case: n b gb hq => [|n] b gb hq.
  + exact: cohomology_middle_cycle gb.
  + have [c hc] := gb.
    have [t ht] := @short_exact_surjective R A B C f g s n c.
    pose v := cycle_inclusion B n.+1 b - cochain_d B n t.
    have vc : cocycle B n.+1 v.
      rewrite /cocycle /v linearB cochain_d2 subr0.
      exact: (submodule_val_mem b).
    have vg : cochain_map_at g n.+1 v = 0.
      by rewrite /v linearB -cochain_map_commutes ht hc subrr.
    have [a ha] := cohomology_middle_cycle (b := cycle_of_cocycle vc) vg.
    exists a; rewrite ha; apply/cohomology_pi_eq.
    change (exists w, cochain_d B n w = v - cycle_inclusion B n.+1 b).
    exists (-t); rewrite linearN /v.
    by rewrite addrAC subrr add0r.
- move=> [a <-]; have [z <-] := quotient_pi_surjective a.
  rewrite !cohomology_map_pi.
  apply/quotient_pi_kernel.
  have hz : cycle_map g n (cycle_map f n z) = 0.
    apply submodule_val_injective.
    change (cochain_map_at g n (cochain_map_at f n (cycle_inclusion A n z)) = 0).
    exact: (@short_exact_composite R A B C f g s n).
  rewrite hz; exact: subspace_zero.
Qed.

Lemma cohomology_quotient_injective n
    (hA : forall a : cohomology A n, a = 0) :
  injective (cohomology_map g n).
Proof.
move=> x y hxy.
have hz : cohomology_map g n (x - y) = 0 by rewrite linearB hxy subrr.
have [a ha] := proj1 (cohomology_middle_exact _) hz.
rewrite (hA a) linear0 in ha.
exact: subr0_eq (esym ha).
Qed.

Lemma cohomology_quotient_surjective n
    (hA : forall a : cohomology A n.+1, a = 0) :
  forall c : cohomology C n, exists b, cohomology_map g n b = c.
Proof.
move=> c; apply/(connecting_map_kernel s c); exact: hA.
Qed.

Lemma cohomology_inclusion_surjective n
    (hC : forall c : cohomology C n, c = 0) :
  forall b : cohomology B n, exists a, cohomology_map f n a = b.
Proof.
move=> b; apply/(cohomology_middle_exact b); exact: hC.
Qed.

Definition cohomology_quotient_iso n
    (hA : forall a : cohomology A n, a = 0)
    (hA' : forall a : cohomology A n.+1, a = 0) :
  @isomorphism (module_category R) (cohomology B n) (cohomology C n) :=
  linear_bijection_iso (cohomology_quotient_injective hA)
    (cohomology_quotient_surjective hA').

End ShortExactMaps.
