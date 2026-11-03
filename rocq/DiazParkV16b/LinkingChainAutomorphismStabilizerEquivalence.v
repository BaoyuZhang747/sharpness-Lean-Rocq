(** Literal mutually inverse group maps for top evaluation, and the
    exact chain automorphism order. *)
From mathcomp Require Import all_boot all_fingroup quotient center.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingSystemAutomorphismProjection LinkingSystemAutomorphismProjectionKernel
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainStabilizer
  LinkingChainAutomorphismStabilizerRestrictions LinkingChainAutomorphismStabilizer.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPCentricLinking DPLinkingAutomorphisms DPLinkingChains
  DPLinkingChainAutomorphisms DPNormalizerChainStabilizer
  DPLinkingChainStabilizerRestrictions DPLinkingChainStabilizer.
Local Open Scope group_scope.

Module DPLinkingChainStabilizerEquivalence.
Section Equivalence.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation G := (automorphism_group L (top c)).
Local Notation C := (chain_automorphism_group L c).
Local Notation AF := (DPFusionSaturation.aut_group F (val (top c))).
Local Notation H := [subg AF]%type.
Local Notation K := (fusion_stabilizer c).
Local Notation T := [subg (top_stabilizer L c)]%type.
Local Notation tp := (top_morphism L c).

Definition top_equivalence_value (a : C) : T.
Proof.
apply: (Sub (tp a)); rewrite top_stabilizer_mem; exact: top_projection_stabilizes.
Defined.

Lemma top_equivalence_value_mul (a b : C) :
  top_equivalence_value (a * b) = top_equivalence_value a * top_equivalence_value b.
Proof. apply val_inj; exact: morphM (in_setT a) (in_setT b). Qed.

Definition top_equivalence : {morphism [set: C] >-> T}.
Proof.
apply: (Morphism (mfun := top_equivalence_value)); move=> a b _ _.
exact: top_equivalence_value_mul.
Defined.

Lemma top_equivalence_apply (a : C) : val (top_equivalence a) = tp a.
Proof. reflexivity. Qed.

Lemma stabilizer_value_mem (a : T) :
  val (DPLinkingAutomorphismProjection.projection L (top c) (val a)) \in K.
Proof. by move: (valP a); rewrite top_stabilizer_mem. Qed.

Definition top_inverse_value (a : T) : C :=
  @compatible_lift S F L c (val a) (stabilizer_value_mem a).

Lemma top_inverse_top (a : T) : tp (top_inverse_value a) = val a.
Proof. exact: compatible_lift_top. Qed.

Theorem top_inverse_equivalence : cancel top_equivalence top_inverse_value.
Proof.
move=> a; apply: (@top_morphism_injective S F L c).
rewrite top_inverse_top; reflexivity.
Qed.

Theorem top_equivalence_inverse : cancel top_inverse_value top_equivalence.
Proof. move=> a; apply val_inj; rewrite top_equivalence_apply; exact: top_inverse_top. Qed.

Lemma top_inverse_value_mul (a b : T) :
  top_inverse_value (a * b) = top_inverse_value a * top_inverse_value b.
Proof.
apply: (@top_morphism_injective S F L c).
by rewrite (morphM tp (in_setT _) (in_setT _)) !top_inverse_top.
Qed.

Definition top_inverse : {morphism [set: T] >-> C}.
Proof.
apply: (Morphism (mfun := top_inverse_value)); move=> a b _ _.
exact: top_inverse_value_mul.
Defined.

Theorem top_equivalence_isom : isom [set: C] [set: T] top_equivalence.
Proof.
apply/isomP; split.
- apply/injmP=> a b _ _ he.
  have hh := congr1 top_inverse_value he.
  by rewrite !top_inverse_equivalence in hh.
- apply/setP=> a; rewrite inE; apply/morphimP.
  exists (top_inverse a); [by rewrite inE | by rewrite inE |].
  symmetry; exact: top_equivalence_inverse.
Qed.

Theorem fusion_stabilizer_subgroup_card : #|fusion_stabilizer_subgroup c| = #|K|.
Proof.
have hK : K \subset (@sgval _ AF) @* [set: H].
  rewrite im_sgval; exact: fusion_stabilizer_sub.
have hc := card_morphpre hK.
by rewrite ker_sgval cards1 mul1n in hc.
Qed.

Theorem chain_automorphism_order : #|C| = (#|'Z(val (top c))| * #|K|)%N.
Proof.
rewrite -(cardsT C) -(card_injm (@top_morphism_injm S F L c) (subxx [set: C])) top_image.
rewrite /top_stabilizer DPLinkingAutomorphismKernel.projection_preimage_card
  fusion_stabilizer_subgroup_card.
reflexivity.
Qed.
End Equivalence.
End DPLinkingChainStabilizerEquivalence.

Check DPLinkingChainStabilizerEquivalence.top_equivalence.
Check DPLinkingChainStabilizerEquivalence.top_inverse.
Check DPLinkingChainStabilizerEquivalence.chain_automorphism_order.
Print Assumptions DPLinkingChainStabilizerEquivalence.top_equivalence_isom.
Print Assumptions DPLinkingChainStabilizerEquivalence.top_inverse_equivalence.
Print Assumptions DPLinkingChainStabilizerEquivalence.top_equivalence_inverse.
Print Assumptions DPLinkingChainStabilizerEquivalence.chain_automorphism_order.
