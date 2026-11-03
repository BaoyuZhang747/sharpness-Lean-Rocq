(** Inverses and endpoints for actual bijective increasing chain selectors. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionSystems.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndices.

Module DPNormalizerChainIndexIsomorphisms.
Section Inverse.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.
Variable e : selector c d.
Hypothesis be : bijective (index e).

Lemma index_onto i : i \in codom (index e).
Proof.
have [r _ hr] := be; apply/codomP; exists (r i); exact: esym (hr i).
Qed.

Definition inverse_index i : 'I_(length d).+1 := iinv (index_onto i).

Lemma inverse_index_right i : index e (inverse_index i) = i.
Proof. exact: f_iinv. Qed.

Lemma inverse_index_left i : inverse_index (index e i) = i.
Proof. apply (@index_injective S F c d e); exact: inverse_index_right. Qed.

Lemma inverse_index_strict (i j : 'I_(length c).+1) :
  i < j -> inverse_index i < inverse_index j.
Proof.
move=> hij; rewrite ltnNge; apply/negP=> hji.
have h := index_mono e hji; rewrite !inverse_index_right in h.
by move: hij; rewrite ltnNge h.
Qed.

Definition inverse_selector : selector d c.
Proof.
apply: (Sub [ffun i => inverse_index i]); apply/increasingP=> i j hij.
rewrite !ffunE; exact: inverse_index_strict hij.
Defined.

Lemma inverse_selector_index i : index inverse_selector i = inverse_index i.
Proof. exact: ffunE. Qed.

Lemma index_top : index e ord_max = ord_max.
Proof.
have h := @index_mono S F c d e (inverse_index ord_max) ord_max
  (leq_ord (inverse_index ord_max)).
rewrite inverse_index_right in h.
apply val_inj; apply/eqP; rewrite eqn_leq; apply/andP; split=> //.
exact: leq_ord.
Qed.

Lemma index_bottom : index e ord0 = ord0.
Proof.
have h := @index_mono S F c d e ord0 (inverse_index ord0)
  (leq0n (inverse_index ord0)).
rewrite inverse_index_right in h.
apply val_inj; apply/eqP; rewrite eqn_leq; apply/andP; split=> //.
Qed.

Lemma inverse_selector_bijective : bijective (index inverse_selector).
Proof.
exists (index e).
- move=> i; rewrite inverse_selector_index; exact: inverse_index_right.
- move=> i; rewrite inverse_selector_index; exact: inverse_index_left.
Qed.

End Inverse.
End DPNormalizerChainIndexIsomorphisms.
