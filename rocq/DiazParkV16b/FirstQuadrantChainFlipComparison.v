(** Literal naturality of the flip isomorphism and actual rowwise comparison. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps
  ChainDegreewiseIso ChainQuasiIsomorphism FirstQuadrantChainBicomplex
  FirstQuadrantChainTotal FirstQuadrantChainTotalMaps FirstQuadrantChainTotalAcyclic
  FirstQuadrantChainComparison FirstQuadrantChainFlip FirstQuadrantChainFlipTotal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps DPChainDegreewiseIso
  DPChainQuasiIsomorphism DPFirstQuadrantChain DPFirstQuadrantChainTotal
  DPFirstQuadrantChainTotalMaps DPFirstQuadrantChainTotalAcyclic DPFirstQuadrantChainComparison
  DPFirstQuadrantChainFlip DPFirstQuadrantChainFlipTotal.
Local Open Scope ring_scope.

Module DPFirstQuadrantChainFlipComparison.
Section Homology.
Variable R : pzRingType.
Variable K : bicomplex R.

Lemma flip_homology_left n (x : homology (total_complex (flip K)) n) :
  homology_map (unflip_total_map K) n (homology_map (flip_total_map K) n x) = x.
Proof. exact: inverse_homology_left. Qed.

Lemma flip_homology_right n (y : homology (total_complex K) n) :
  homology_map (flip_total_map K) n (homology_map (unflip_total_map K) n y) = y.
Proof. exact: inverse_homology_right. Qed.

Lemma flip_homology_injective n : injective (homology_map (flip_total_map K) n).
Proof. exact (can_inj (@flip_homology_left n)). Qed.

Theorem row_acyclic_total (hrows : forall q, acyclic (horizontal_complex K q)) :
  acyclic (total_complex K).
Proof.
have hf : acyclic (total_complex (flip K)).
  apply: total_acyclic=> p; rewrite flip_vertical; exact: hrows.
move=> n y hy.
have hx := @chain_map_cycle R _ _ (unflip_total_map K) n y hy.
have [z hz] := @hf n _ hx.
exists (chain_map_at (flip_total_map K) n.+1 z).
rewrite chain_map_commutes hz; exact: unflip_total_right.
Qed.
End Homology.

Section Maps.
Variable R : pzRingType.
Variables K L : bicomplex R.
Variable f : bicomplex_map K L.

Lemma flip_total_naturality n (a : total_term (flip K) n) :
  chain_map_at (total_map f) n (chain_map_at (flip_total_map K) n a) =
  chain_map_at (flip_total_map L) n (chain_map_at (total_map (flip_map f)) n a).
Proof.
apply functional_extensionality_dep=> p;
 apply functional_extensionality_dep=> q; apply functional_extensionality_dep=> h.
change (bicomplex_map_at f p q ((-1:R)^+(p*q) *: a q p (swap_index h)) =
 (-1:R)^+(p*q) *: bicomplex_map_at f p q (a q p (swap_index h))).
exact: linearZ.
Qed.

Lemma flip_homology_naturality n (a : homology (total_complex (flip K)) n) :
  homology_map (total_map f) n (homology_map (flip_total_map K) n a) =
  homology_map (flip_total_map L) n (homology_map (total_map (flip_map f)) n a).
Proof.
have [z <-] := quotient_pi_surjective a; rewrite !homology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective.
exact: flip_total_naturality.
Qed.

Theorem row_total_map_quasi_isomorphism
    (hrows : forall q, quasi_isomorphism (horizontal_map f q)) :
  quasi_isomorphism (total_map f).
Proof.
have hf : quasi_isomorphism (total_map (flip_map f)).
  apply: total_map_quasi_isomorphism=> p; rewrite flip_vertical_map; exact: hrows.
move=> n; split.
- move=> x y h.
  have he : homology_map (unflip_total_map K) n x = homology_map (unflip_total_map K) n y.
    apply (proj1 (hf n)); apply: (@flip_homology_injective R L n).
    by rewrite -!flip_homology_naturality !flip_homology_right h.
  by rewrite -(flip_homology_right x) -(flip_homology_right y) he.
- move=> y.
  have [x hx] := proj2 (hf n) (homology_map (unflip_total_map L) n y).
  exists (homology_map (flip_total_map K) n x).
  by rewrite flip_homology_naturality hx flip_homology_right.
Qed.

End Maps.
End DPFirstQuadrantChainFlipComparison.
