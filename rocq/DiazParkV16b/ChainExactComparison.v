(** A map of actual short exact chain sequences: two homology isomorphisms give the third. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainShortExact ChainConnecting ChainLongExact ChainConnectingNaturality
  ChainHomologySquares LinearFiveLemma LinearCokernelComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPChainComplex DPChainHomology DPChainHomologyMaps DPChainShortExact
  DPChainConnecting DPChainLongExact DPChainConnectingNaturality DPChainHomologySquares
  DPLinearFiveLemma DPLinearCokernelComparison.

Module DPChainExactComparison.
Section Comparison.
Variable R : pzRingType.
Variables A B C A' B' C' : chain_complex R.
Variables (f : chain_map A B) (g : chain_map B C)
  (f' : chain_map A' B') (g' : chain_map B' C').
Variables (s : chain_short_exact f g) (s' : chain_short_exact f' g').
Variables (u : chain_map A A') (v : chain_map B B') (w : chain_map C C').
Variable hleft : forall n x, chain_map_at v n (chain_map_at f n x) =
  chain_map_at f' n (chain_map_at u n x).
Variable hright : forall n x, chain_map_at w n (chain_map_at g n x) =
  chain_map_at g' n (chain_map_at v n x).
Variable hui : forall n, injective (homology_map u n).
Variable hus : forall n y, exists x, homology_map u n x = y.
Variable hvi : forall n, injective (homology_map v n).
Variable hvs : forall n y, exists x, homology_map v n x = y.

Definition positive_comparison_iso n : @isomorphism (module_category R)
    [the lmodType R of homology C n.+1] [the lmodType R of homology C' n.+1] :=
  @five_iso R (homology A n.+1) (homology B n.+1) (homology C n.+1)
    (homology A n) (homology B n)
    (homology A' n.+1) (homology B' n.+1) (homology C' n.+1)
    (homology A' n) (homology B' n)
    (homology_map f n.+1) (homology_map g n.+1) (connecting_map s n) (homology_map f n)
    (homology_map f' n.+1) (homology_map g' n.+1) (connecting_map s' n) (homology_map f' n)
    (homology_map u n.+1) (homology_map v n.+1) (homology_map w n.+1)
    (homology_map u n) (homology_map v n)
    (@homology_square R A B A' B' f u v f' hleft n.+1)
    (@homology_square R B C B' C' g v w g' hright n.+1)
    (fun q => esym (@connecting_natural R A B C A' B' C' f g f' g' s s' u v w hleft hright n q))
    (@homology_square R A B A' B' f u v f' hleft n)
    (@homology_middle_exact R A B C f g s n.+1)
    (@connecting_map_kernel R A B C f g s n)
    (@connecting_map_image R A B C f g s n)
    (@homology_middle_exact R A' B' C' f' g' s' n.+1)
    (@connecting_map_kernel R A' B' C' f' g' s' n)
    (@connecting_map_image R A' B' C' f' g' s' n)
    (@hus n.+1) (@hvi n.+1) (@hvs n.+1) (@hui n) (@hus n) (@hvi n).

Definition zero_comparison_iso : @isomorphism (module_category R)
    [the lmodType R of homology C 0%N] [the lmodType R of homology C' 0%N] :=
  @cokernel_iso R (homology A 0%N) (homology B 0%N) (homology C 0%N)
    (homology A' 0%N) (homology B' 0%N) (homology C' 0%N)
    (homology_map f 0%N) (homology_map g 0%N) (homology_map f' 0%N) (homology_map g' 0%N)
    (homology_map u 0%N) (homology_map v 0%N) (homology_map w 0%N)
    (@homology_square R A B A' B' f u v f' hleft 0%N)
    (@homology_square R B C B' C' g v w g' hright 0%N)
    (@homology_middle_exact R A B C f g s 0%N)
    (@homology_middle_exact R A' B' C' f' g' s' 0%N)
    (@homology_zero_surjective R A B C f g s)
    (@homology_zero_surjective R A' B' C' f' g' s')
    (@hus 0%N) (@hvi 0%N) (@hvs 0%N).

Definition comparison_iso n : @isomorphism (module_category R)
    [the lmodType R of homology C n] [the lmodType R of homology C' n] :=
  match n with 0%N => zero_comparison_iso | k.+1 => positive_comparison_iso k end.

Theorem comparison_iso_hom n (q : homology C n) :
  module_hom_fun (iso_hom (comparison_iso n)) q = homology_map w n q.
Proof. by case: n q. Qed.
End Comparison.
End DPChainExactComparison.
