(** Actual quotient-chain isomorphism from a proved intersection--union sequence. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import ChainComplex ChainHomology ChainHomologyMaps ChainSubcomplex
  ChainSubcomplexMaps ChainMapImage ChainDegreewiseIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPChainHomology DPChainHomologyMaps DPChainSubcomplex
  DPChainSubcomplexMaps DPChainMapImage DPChainDegreewiseIso.
Local Open Scope ring_scope.

Module DPSingularExcisionQuotientAlgebra.
Section QuotientUnion.
Variable R : pzRingType.
Variables I A B S : chain_complex R.
Variables (f : chain_map I A) (j : chain_map I B) (k : chain_map A S) (l : chain_map B S).
Variable hsquare : forall n x, chain_map_at k n (chain_map_at f n x) = chain_map_at l n (chain_map_at j n x).
Variable hkernel : forall n a b, chain_map_at k n a + chain_map_at l n b = 0 ->
  exists c, chain_map_at f n c = a /\ - chain_map_at j n c = b.
Variable hsurj : forall n s, exists a b, chain_map_at k n a + chain_map_at l n b = s.

Definition quotient_union_preserves n x :
  subspace_at (image_subcomplex f) n x ->
  subspace_at (image_subcomplex l) n (chain_map_at k n x).
Proof. move=> [y <-]; exists (chain_map_at j n y); symmetry; exact: hsquare. Defined.

Definition quotient_union_map : chain_map (relative_chain f) (relative_chain l) :=
  @relative_map R A S k (image_subcomplex f) (image_subcomplex l) quotient_union_preserves.

Lemma quotient_union_projection n a :
  chain_map_at quotient_union_map n (chain_map_at (relative_projection f) n a) =
  chain_map_at (relative_projection l) n (chain_map_at k n a).
Proof. exact: relative_map_projection. Qed.

Lemma quotient_union_kernel_zero n q : chain_map_at quotient_union_map n q = 0 -> q = 0.
Proof.
case: (@relative_projection_surjective R I A f n q) => a <-.
rewrite quotient_union_projection => h.
case: (proj1 (@relative_sequence_exact R B S l n _) h) => b hb.
have he : chain_map_at k n a + chain_map_at l n (-b) = 0.
  by rewrite linearN -hb subrr.
case: (@hkernel n a (-b) he) => c [hc _].
apply: (proj2 (@relative_sequence_exact R I A f n _)); by exists c.
Qed.

Lemma quotient_union_injective n : injective (chain_map_at quotient_union_map n).
Proof.
move=> a b h; apply/eqP; rewrite -subr_eq0.
apply/eqP; apply: quotient_union_kernel_zero.
by rewrite linearB h subrr.
Qed.

Lemma quotient_union_surjective n q : exists a, chain_map_at quotient_union_map n a = q.
Proof.
case: (@relative_projection_surjective R B S l n q) => s <-.
case: (@hsurj n s) => a [b hab].
exists (chain_map_at (relative_projection f) n a).
rewrite quotient_union_projection -hab linearD relative_projection_annihilates addr0.
reflexivity.
Qed.

Definition quotient_union_inverse : chain_map (relative_chain l) (relative_chain f) :=
  inverse_chain (@quotient_union_injective) (@quotient_union_surjective).

Definition quotient_union_homology_iso n : @isomorphism (module_category R)
  (homology (relative_chain f) n) (homology (relative_chain l) n) :=
  degreewise_homology_iso (@quotient_union_injective) (@quotient_union_surjective) n.

Lemma quotient_union_homology_iso_hom n q :
  module_hom_fun (iso_hom (quotient_union_homology_iso n)) q = homology_map quotient_union_map n q.
Proof. reflexivity. Qed.
End QuotientUnion.
End DPSingularExcisionQuotientAlgebra.
