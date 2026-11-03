(** Actual strict-chain prefix insertion and its increasing selectors.
    The finite length bound is derived by the original full chain constructor. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndices.

Module DPNormalizerPointedChainPrefix.
Section Ordinals.
Variable T : Type.
Variable n : nat.
Variable b : T.
Variable f : 'I_n.+1 -> T.
Definition cons (i : 'I_n.+2) : T :=
  if unlift ord0 i is Some j then f j else b.
Lemma cons_zero : cons ord0 = b.
Proof. by rewrite /cons unlift_none. Qed.
Lemma cons_lift i : cons (lift ord0 i) = f i.
Proof. by rewrite /cons liftK. Qed.
End Ordinals.

Section Chains.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom c).

Definition prefix_entries := [ffun i => cons I (entry c) i].

Lemma prefix_entries_strict : strict_entries prefix_entries.
Proof.
apply/strict_entriesP=> i j hij; rewrite /prefix_entries !ffunE.
case: (unliftP ord0 i) hij=> [i' ->|->] hij;
  case: (unliftP ord0 j) hij=> [j' ->|->] hij.
- rewrite !cons_lift; apply: entry_strict; by rewrite !lift0 ltnS in hij.
- by rewrite ltn0 in hij.
- rewrite cons_zero cons_lift.
  exact: proper_sub_trans hI (@entry_mono S F c ord0 j' (leq0n j')).
- by rewrite ltnn in hij.
Qed.

Definition prepend : chain F := of_entries prefix_entries_strict.
Lemma prepend_length : length prepend = (length c).+1.
Proof. reflexivity. Qed.
Lemma prepend_entry_zero : entry prepend ord0 = I.
Proof. by rewrite /prepend of_entries_entry /prefix_entries ffunE cons_zero. Qed.
Lemma prepend_entry_lift i : entry prepend (lift ord0 i) = entry c i.
Proof. by rewrite /prepend of_entries_entry /prefix_entries ffunE cons_lift. Qed.
Lemma prepend_bottom : bottom prepend = I.
Proof. exact prepend_entry_zero. Qed.
Lemma prepend_top : top prepend = top c.
Proof.
have he : (ord_max : 'I_(length c).+2) = lift ord0 (ord_max : 'I_(length c).+1).
  apply val_inj; reflexivity.
rewrite /top he; exact: prepend_entry_lift.
Qed.

Definition deletion_selector : selector prepend c.
Proof.
apply: (Sub [ffun i => lift ord0 i]); apply/increasingP=> i j hij.
by rewrite !ffunE !lift0 ltnS.
Defined.
Lemma deletion_index i : index deletion_selector i = lift ord0 i.
Proof. exact: ffunE. Qed.
End Chains.

Section ExtensionSelector.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables c d : chain F.
Variable I : DPFusionOrbit.centric_object F.
Hypothesis hI : val I \proper val (bottom d).
Variable e : selector c d.
Hypothesis hpos : 0 < index e ord0.

Definition extended_selector : selector c (prepend hI).
Proof.
apply: (Sub [ffun i => cons ord0 (index e) i]); apply/increasingP=> i j hij.
rewrite !ffunE.
case: (unliftP ord0 i) hij=> [i' ->|->] hij;
  case: (unliftP ord0 j) hij=> [j' ->|->] hij.
- rewrite !cons_lift; apply: index_strict; by rewrite !lift0 ltnS in hij.
- by rewrite ltn0 in hij.
- rewrite cons_zero cons_lift.
  exact (leq_trans hpos (@index_mono S F c d e ord0 j' (leq0n j'))).
- by rewrite ltnn in hij.
Defined.
Lemma extended_index_zero : index extended_selector ord0 = ord0.
Proof. by rewrite /extended_selector /index /= ffunE cons_zero. Qed.
Lemma extended_index_lift i : index extended_selector (lift ord0 i) = index e i.
Proof. by rewrite /extended_selector /index /= ffunE cons_lift. Qed.
Lemma extended_index_last : index extended_selector ord_max = index e ord_max.
Proof.
have he : (ord_max : 'I_(length d).+2) = lift ord0 (ord_max : 'I_(length d).+1).
  apply val_inj; reflexivity.
rewrite he; exact: extended_index_lift.
Qed.
End ExtensionSelector.
End DPNormalizerPointedChainPrefix.
