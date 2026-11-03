(** An increasing selection of all entries of the same finite chain is identity. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices
  NormalizerChainIndexIsomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndices DPNormalizerChainIndexIsomorphisms.

Module DPNormalizerChainEndoselection.

Lemma strict_ordinal_self_le n (f : 'I_n -> 'I_n)
    (hf : forall i j : 'I_n, i < j -> f i < f j) : forall i : 'I_n, i <= f i.
Proof.
have h : forall k, forall i : 'I_n, val i = k -> k <= f i.
  elim=> [|k IH] i hi; first exact: leq0n.
  have hk : k < n by apply: ltn_trans _ (ltn_ord i); rewrite hi.
  pose j : 'I_n := Ordinal hk.
  have hj : j < i by change (k < val i); rewrite hi.
  have he := hf j i hj.
  have hl := IH j erefl.
  exact: leq_ltn_trans hl he.
move=> i; exact: h (val i) i erefl.
Qed.

Section Chains.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.
Variable e : selector c c.

Theorem endoselection_index i : index e i = i.
Proof.
have be := equal_length_bijective e erefl.
have h1 := strict_ordinal_self_le (@index_strict S F c c e) i.
have h2 := strict_ordinal_self_le
  (@index_strict S F c c (inverse_selector be)) (index e i).
rewrite inverse_selector_index inverse_index_left in h2.
apply/val_inj/eqP; rewrite eqn_leq; exact/andP.
Qed.

Theorem endoselection_identity : e = identity c.
Proof.
apply: val_inj; apply/ffunP=> i.
change (index e i = index (identity c) i).
by rewrite endoselection_index identity_index.
Qed.

End Chains.
End DPNormalizerChainEndoselection.
