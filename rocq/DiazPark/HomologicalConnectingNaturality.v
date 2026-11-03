From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalConnecting MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalConnecting.

Module DiazParkHomologicalConnectingNaturality.
Section Naturality.
Variable R : pzRingType.
Variables A B C A' B' C' : @cochain_complex R.
Variables (f : cochain_map A B) (g : cochain_map B C)
  (f' : cochain_map A' B') (g' : cochain_map B' C').
Variables (s : degreewise_short_exact f g) (s' : degreewise_short_exact f' g').
Variables (u : cochain_map A A') (v : cochain_map B B') (w : cochain_map C C').
Hypothesis hf : forall n a, cochain_map_at f' n (cochain_map_at u n a) =
  cochain_map_at v n (cochain_map_at f n a).
Hypothesis hg : forall n b, cochain_map_at g' n (cochain_map_at v n b) =
  cochain_map_at w n (cochain_map_at g n b).

Theorem connecting_map_naturality n (q : cohomology C n) :
  connecting_map s' n (cohomology_map w n q) =
    cohomology_map u n.+1 (connecting_map s n q).
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite cohomology_map_pi !connecting_map_pi /connecting_class cohomology_map_pi.
apply: (@connecting_class_solution R A' B' C' f' g' s' n (cycle_map w n z)
  (cochain_map_at v n (connecting_lift s z)) (cycle_map u n.+1 (connecting_cycle s z))).
- change (cochain_map_at g' n (cochain_map_at v n (connecting_lift s z)) =
    cochain_map_at w n (cycle_inclusion C n z)).
  by rewrite hg connecting_lift_spec.
- change (cochain_map_at f' n.+1 (cochain_map_at u n.+1 (connecting_preimage s z)) =
    cochain_d B' n (cochain_map_at v n (connecting_lift s z))).
  by rewrite hf connecting_preimage_spec cochain_map_commutes.
Qed.

End Naturality.
End DiazParkHomologicalConnectingNaturality.
