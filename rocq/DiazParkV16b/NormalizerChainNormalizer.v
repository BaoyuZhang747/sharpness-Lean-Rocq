(** The literal simultaneous normalizer of every entry of a strict chain. *)
From mathcomp Require Import all_boot all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains.
Local Open Scope group_scope.

Module DPNormalizerChain.
Section Normalizer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.

Definition normalizer : {group S} := (\bigcap_i 'N(subgroup c i))%G.

Lemma normalizerP x : reflect
  (forall i : 'I_(length c).+1, x \in 'N(subgroup c i)) (x \in normalizer).
Proof.
apply: (iffP bigcapP).
- move=> h i; exact: h i isT.
- move=> h i _; exact: h.
Qed.

Lemma normalizer_sub (i : 'I_(length c).+1) : normalizer \subset 'N(subgroup c i).
Proof. apply/subsetP=> x /normalizerP hx; exact: hx. Qed.

Lemma bottom_sub_normalizer : val (bottom c) \subset normalizer.
Proof.
apply/subsetP=> x hx; apply/normalizerP=> i.
have hi : x \in subgroup c i :=
  subsetP (@entry_mono S F c ord0 i (leq0n i)) x hx.
exact (subsetP (normG (subgroup c i)) x hi).
Qed.

Lemma normalizer_sub_top : normalizer \subset 'N(val (top c)).
Proof. exact: normalizer_sub ord_max. Qed.

Lemma normalizer_pgroup (pi : nat_pred) : pi.-group [set: S] -> pi.-group normalizer.
Proof. exact: pgroupS (subsetT normalizer). Qed.

End Normalizer.
End DPNormalizerChain.

Print Assumptions DPNormalizerChain.normalizerP.
Print Assumptions DPNormalizerChain.bottom_sub_normalizer.
