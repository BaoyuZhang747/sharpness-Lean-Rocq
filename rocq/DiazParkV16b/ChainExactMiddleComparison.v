(** A literal map of short exact chain sequences: left and right quasi-isomorphisms imply the middle one, including H0. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure HomologicalModuleIso MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
 ChainShortExact ChainConnecting ChainLongExact ChainConnectingNaturality ChainHomologySquares ChainQuasiIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPChainComplex DPChainHomology DPChainHomologyMaps
 DPChainShortExact DPChainConnecting DPChainLongExact DPChainConnectingNaturality DPChainHomologySquares DPChainQuasiIsomorphism.
Local Open Scope ring_scope.
Module DPChainExactMiddleComparison.
Section Comparison.
Variable R : pzRingType.
Variables A B C A' B' C' : chain_complex R.
Variables (f:chain_map A B) (g:chain_map B C) (f':chain_map A' B') (g':chain_map B' C').
Variables (s:chain_short_exact f g) (s':chain_short_exact f' g').
Variables (u:chain_map A A') (v:chain_map B B') (w:chain_map C C').
Variable hleft : forall n x, chain_map_at v n (chain_map_at f n x)=chain_map_at f' n (chain_map_at u n x).
Variable hright : forall n x, chain_map_at w n (chain_map_at g n x)=chain_map_at g' n (chain_map_at v n x).
Variables (hu:quasi_isomorphism u) (hw:quasi_isomorphism w).
Local Notation left_square := (@homology_square R A B A' B' f u v f' hleft).
Local Notation right_square := (@homology_square R B C B' C' g v w g' hright).
Local Notation delta_square := (@connecting_natural R A B C A' B' C' f g f' g' s s' u v w hleft hright).

Theorem middle_homology_injective n : injective (homology_map v n).
Proof.
have ker : forall x, homology_map v n x=0 -> x=0.
  move=>x hx.
  have gx : homology_map g n x=0.
    apply (proj1 (hw n)); by rewrite linear0 right_square hx linear0.
  have [a ha] := proj1 (@homology_middle_exact R A B C f g s n x) gx.
  have fua : homology_map f' n (homology_map u n a)=0.
    by rewrite -left_square ha hx.
  have [z' hz'] := proj1 (@connecting_map_image R A' B' C' f' g' s' n _) fua.
  have [z hz] := proj2 (hw n.+1) z'.
  have ea : connecting_map s n z=a.
    apply (proj1 (hu n)); by rewrite -delta_square hz hz'.
  rewrite -ha -ea; apply (proj2 (@connecting_map_image R A B C f g s n _)); by exists z.
move=>x y hxy; apply/subr0_eq; apply (ker (x-y)).
change (homology_map v n (x-y)=0); by rewrite linearB hxy subrr.
Qed.

Lemma middle_lift_correction n (y:homology B' n) (x:homology B n)
 (hx:homology_map w n (homology_map g n x)=homology_map g' n y) :
 exists t, homology_map v n t=y.
Proof.
have hker : homology_map g' n (y-homology_map v n x)=0.
  by rewrite linearB -right_square hx subrr.
have [a' ha'] := proj1 (@homology_middle_exact R A' B' C' f' g' s' n _) hker.
have [a ha] := proj2 (hu n) a'.
exists (x+homology_map f n a).
rewrite linearD left_square ha ha'; by rewrite addrC subrK.
Qed.

Theorem middle_homology_surjective_positive n (y:homology B' n.+1) :
 exists x, homology_map v n.+1 x=y.
Proof.
have [z hz] := proj2 (hw n.+1) (homology_map g' n.+1 y).
have dz : connecting_map s n z=0.
  apply (proj1 (hu n)); rewrite linear0 -delta_square hz.
  apply (proj2 (@connecting_map_kernel R A' B' C' f' g' s' n _)); by exists y.
have [x hx] := proj1 (@connecting_map_kernel R A B C f g s n z) dz.
apply: (@middle_lift_correction n.+1 y x); by rewrite hx hz.
Qed.

Theorem middle_homology_surjective_zero (y:homology B' 0%N) :
 exists x, homology_map v 0%N x=y.
Proof.
have [z hz] := proj2 (hw 0%N) (homology_map g' 0%N y).
have [x hx] := @homology_zero_surjective R A B C f g s z.
apply: (@middle_lift_correction 0%N y x); by rewrite hx hz.
Qed.

Theorem middle_quasi_isomorphism : quasi_isomorphism v.
Proof.
move=>n; split; first exact: middle_homology_injective.
case: n=>[|n]; [exact: middle_homology_surjective_zero | exact: middle_homology_surjective_positive].
Qed.

Definition middle_homology_iso n : @isomorphism (module_category R)
 [the lmodType R of homology B n] [the lmodType R of homology B' n] :=
 @linear_bijection_iso R _ _ (homology_map v n)
 (proj1 (middle_quasi_isomorphism n)) (proj2 (middle_quasi_isomorphism n)).
Lemma middle_homology_iso_forward n (x:homology B n) :
 module_hom_fun (iso_hom (middle_homology_iso n)) x=homology_map v n x.
Proof. reflexivity. Qed.
End Comparison.
End DPChainExactMiddleComparison.
