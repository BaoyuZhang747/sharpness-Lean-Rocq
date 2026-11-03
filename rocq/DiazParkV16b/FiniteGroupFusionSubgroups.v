(** Literal subgroup and conjugacy transport for the induced fusion system. *)
From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionConjugacy
  FusionCentralizerMaps.
From DiazParkV16b Require Import FiniteGroupFusion.
Import DPFusion DPFusionSubgroup DPFiniteGroupFusion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFiniteGroupFusionSubgroups.
Section Transport.
Variable G : finGroupType.
Variable T : {group G}.
Local Notation S := [subg T]%type.

Lemma ambient_card (P : {group S}) : #|ambient P| = #|P|.
Proof.
change (#|sgval @* P| = #|P|).
by rewrite (card_injm (injm_sgval T) (subsetT P)).
Qed.

Lemma ambient_top : ambient [set: S]%G = T.
Proof. apply: val_inj; exact: im_sgval. Qed.

Lemma ambient_normalizer (P : {group S}) : ambient 'N(P)%G = 'N_T(ambient P)%G.
Proof.
apply: val_inj; rewrite /ambient /= (injm_norm (injm_sgval T) (subsetT P)).
by rewrite im_sgval.
Qed.

Lemma ambient_centralizer (P : {group S}) : ambient 'C(P)%G = 'C_T(ambient P)%G.
Proof.
apply: val_inj; rewrite /ambient /= (injm_cent (injm_sgval T) (subsetT P)).
by rewrite im_sgval.
Qed.

Definition from_ambient (P : {group G}) : {group S} := (subg T @* P)%G.

Lemma ambient_from (P : {group G}) : P \subset T -> ambient (from_ambient P) = P.
Proof. move=> h; apply: val_inj; exact: subgmK h. Qed.

Lemma from_ambientK (P : {group S}) : from_ambient (ambient P) = P.
Proof. apply: val_inj; exact: sgvalmK. Qed.

Lemma ambient_conjugation_image (P Q : {group S}) (f : DPFusion.map P Q) (g : G) :
  {in P, forall x, val (f x) = (val x) ^ g} ->
  ambient P :^ g = ambient (DPFusion.image f).
Proof.
move=> hg; apply/eqP; rewrite eqEcard; apply/andP; split.
- apply: (@ambient_conjugation_sub G T P (DPFusion.image f) (DPFusion.to_image f) g).
  move=> x Px; by rewrite DPFusion.to_image_in // hg.
- by rewrite cardJg !ambient_card DPFusionConjugacy.map_image_card.
Qed.

Lemma conjugation_map_image (P Q : {group S}) (g : G)
    (h : ambient P :^ g \subset ambient Q) :
  ambient (DPFusion.image (DPFiniteGroupFusion.conjugation_map h)) = ambient P :^ g.
Proof.
apply: val_inj; symmetry.
exact: (ambient_conjugation_image (DPFiniteGroupFusion.conjugation_mapE h)).
Qed.

Lemma conjugateP (P Q : {group S}) :
  reflect (exists g : G, ambient P :^ g = ambient Q)
    (DPFusionSystem.conjugate (DPFiniteGroupFusion.system T) P Q).
Proof.
apply: (iffP existsP).
- move=> [f /andP[/DPFiniteGroupFusion.allowedP[g hg] /eqP hf]].
  exists g; by rewrite (ambient_conjugation_image hg) hf.
- move=> [g hg].
  have h : ambient P :^ g \subset ambient Q by rewrite hg.
  exists (DPFiniteGroupFusion.conjugation_map h); apply/andP; split.
  + exact: DPFiniteGroupFusion.conjugation_map_allowed.
  + apply/eqP; apply: ambient_injective; apply: val_inj.
    exact: eq_trans (esym (ambient_conjugation_image (conjugation_mapE h))) hg.
Qed.

Lemma conjugate_from (P : {group S}) (g : G) (h : ambient P :^ g \subset T) :
  DPFusionSystem.conjugate (DPFiniteGroupFusion.system T) P (from_ambient (ambient P :^ g)%G).
Proof. apply/conjugateP; exists g; by rewrite ambient_from. Qed.

Lemma sylow_carrier_pgroup (p : nat) :
  p.-Sylow([set: G]) T -> p.-group [set: S].
Proof.
move=> sylT.
rewrite -(im_subg T); exact: morphim_pgroup _ (pHall_pgroup sylT).
Qed.

End Transport.
End DPFiniteGroupFusionSubgroups.

Print Assumptions DPFiniteGroupFusionSubgroups.conjugateP.
Print Assumptions DPFiniteGroupFusionSubgroups.ambient_normalizer.
