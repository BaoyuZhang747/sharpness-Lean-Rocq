From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalConnecting HomologicalConnectingNaturality HomologicalDiagramLimits
  MackeyModuleCarriers MackeyModuleQuotient BarComplex BarNaturality BarDegreeZero BarConnectingLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalConnecting DiazParkHomologicalConnectingNaturality
  DiazParkBarComplex DiazParkBarNaturality DiazParkBarDegreeZero DiazParkBarConnectingLimit.

Module DiazParkBarConnectingNaturality.
Section Naturality.
Variable R : pzRingType.
Variable C : category.
Variables A B D A' B' D' : module_codiagram R C.
Variables (f : nat_trans A B) (g : nat_trans B D)
  (f' : nat_trans A' B') (g' : nat_trans B' D').
Variables (s : degreewise_short_exact (bar_cochain_map f) (bar_cochain_map g))
  (s' : degreewise_short_exact (bar_cochain_map f') (bar_cochain_map g')).
Variables (u : nat_trans A A') (v : nat_trans B B') (w : nat_trans D D').
Hypothesis hf : forall x a, module_hom_fun (component f' x) (module_hom_fun (component u x) a) =
  module_hom_fun (component v x) (module_hom_fun (component f x) a).
Hypothesis hg : forall x b, module_hom_fun (component g' x) (module_hom_fun (component v x) b) =
  module_hom_fun (component w x) (module_hom_fun (component g x) b).

Lemma bar_connecting_map_naturality n (q : cohomology (bar_complex D) n) :
  connecting_map s' n (cohomology_map (bar_cochain_map w) n q) =
    cohomology_map (bar_cochain_map u) n.+1 (connecting_map s n q).
Proof.
apply: (@connecting_map_naturality R _ _ _ _ _ _ _ _ _ _ s s'
  (bar_cochain_map u) (bar_cochain_map v) (bar_cochain_map w)).
- move=> k a; apply functional_extensionality_dep => x.
  apply functional_extensionality_dep => p; exact: hf.
- move=> k b; apply functional_extensionality_dep => x.
  apply functional_extensionality_dep => p; exact: hg.
Qed.

Lemma limit_connecting_naturality (z : module_limit_type D) :
  limit_connecting s' (limit_action w z) =
    cohomology_map (bar_cochain_map u) 1 (limit_connecting s z).
Proof.
have he : cycle_map (bar_cochain_map w) 0 (bar_limit_to_cycle D z) =
    bar_limit_to_cycle D' (limit_action w z).
  apply submodule_val_injective; apply functional_extensionality_dep => x.
  apply functional_extensionality_dep => p; case: p.
  change (module_hom_fun (component w x) (module_limit_val z x) =
    module_limit_val (limit_action w z) x).
  by rewrite limit_action_coordinate.
have h := bar_connecting_map_naturality
  (quotient_pi (boundaries_in_cycles (bar_complex D) 0) (bar_limit_to_cycle D z)).
rewrite cohomology_map_pi he !connecting_map_pi in h; exact: h.
Qed.

End Naturality.
End DiazParkBarConnectingNaturality.
