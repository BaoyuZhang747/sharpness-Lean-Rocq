(** A nonvacuous saturated example on the cyclic group of order two. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp.
From DiazPark Require Import FusionSaturation.
From DiazParkV16b Require Import FiniteGroupFusion FiniteGroupFusionSaturation
  FiniteGroupFusionSubgroups.
From DiazParkV29 Require Import RationalMackey.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPV29RationalExample.
Definition ambient := [the finGroupType of 'I_2].
Definition full : {group ambient} := [set: ambient].
Definition example_group := [the finGroupType of [subg full]%type].
Definition example_fusion := DPFiniteGroupFusion.system full.

Lemma full_sylow : 2.-Sylow([set: ambient]) full.
Proof. rewrite /full /pHall subxx indexgg /pgroup cardsT /ambient card_ord. by vm_compute. Qed.

Lemma example_pgroup : 2.-group [set: example_group].
Proof. exact: DPFiniteGroupFusionSubgroups.sylow_carrier_pgroup full_sylow. Qed.

Lemma example_saturated : DPFusionSaturation.saturated example_fusion 2.
Proof. exact: DPFiniteGroupFusionSaturation.saturated full_sylow. Qed.

Lemma example_nontrivial : [set: example_group] != 1%G.
Proof.
apply/eqP => e.
have ec := congr1 (fun X : {set example_group} => #|X|) e.
rewrite cardsT cards1 /example_group card_sub /full cardsT /ambient card_ord in ec.
discriminate.
Qed.

Definition example_counterexample :=
  @DPV29RationalMackey.rational_centralizer_counterexample example_group example_fusion
    example_nontrivial.

End DPV29RationalExample.
