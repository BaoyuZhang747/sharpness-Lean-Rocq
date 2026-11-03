(** The actual subgroup normalizer embeds in linking automorphisms via
    the distinguished transporter functor. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionCentricCriterion.
From DiazParkV16b Require Import LinkingSystemTransporter LinkingSystem LinkingSystemAutomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingTransporter DPCentricLinking DPLinkingAutomorphisms.
Local Open Scope group_scope.

Module DPNormalizerChainTransporter.
Section Normalizer.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable P : DPFusionOrbit.centric_object F.
Local Notation N := [subg 'N(val P)]%type.

Definition normalizer_transporter (s : N) : transporter_hom (val P) (val P).
Proof.
apply: (Sub (val s)); by rewrite (normP (valP s)).
Defined.

Definition normalizer_map (s : N) : automorphism_group L P :=
  linking_transporter L (normalizer_transporter s).

Lemma normalizer_map_one : normalizer_map 1 = 1.
Proof.
have he : normalizer_transporter 1 = DPLinkingTransporter.transporter_identity (val P).
  apply val_inj; reflexivity.
rewrite /normalizer_map he; exact: transporter_identity.
Qed.

Lemma normalizer_map_mul (s t : N) : normalizer_map (s * t) = normalizer_map s * normalizer_map t.
Proof.
have he : normalizer_transporter (s * t) =
    DPLinkingTransporter.transporter_compose (normalizer_transporter s) (normalizer_transporter t).
  apply val_inj; reflexivity.
rewrite /normalizer_map he; exact: transporter_compose.
Qed.

Lemma normalizer_map_morphic : morphic [set: N] normalizer_map.
Proof. apply/morphicP=> s t _ _; exact: normalizer_map_mul. Qed.

Definition normalizer_morphism :
    {morphism [set: N] >-> automorphism_group L P} :=
  [morphism of morphm normalizer_map_morphic].

Lemma normalizer_projection (s : N) x (hx : x \in val P) :
  DPFusion.map_fun (val (linking_projection L (normalizer_map s))) x = x ^ val s.
Proof.
rewrite /normalizer_map projection_transporter.
change (DPFusion.map_fun (DPFusion.conjugation (valP (normalizer_transporter s))) x = x ^ val s).
exact: DPFusion.conjugation_in.
Qed.

Lemma normalizer_map_of_mem (s : N) (hs : val s \in val P) :
  normalizer_map s = distinguished L (Sub (val s) hs).
Proof.
rewrite /normalizer_map /distinguished; congr (linking_transporter L _).
apply val_inj; reflexivity.
Qed.

Theorem normalizer_map_kernel (s : N) : normalizer_map s = 1 -> s = 1.
Proof.
move=> hs.
have hc : val s \in 'C(val P).
  apply/centP=> x hx; apply/esym/commgP/conjg_fixP.
  have he := congr1 (fun a : automorphism_group L P =>
    DPFusion.map_fun (val (linking_projection L a)) x) hs.
  rewrite normalizer_projection // in he.
  change (x ^ val s = DPFusion.map_fun (val (linking_projection L (linking_identity L P))) x) in he.
  rewrite projection_identity in he; exact: eq_trans he (DPFusion.identity_in hx).
have hp : val s \in val P :=
  subsetP (DPFusionCentricCriterion.centric_self_centralizing (valP P)) _ hc.
rewrite (normalizer_map_of_mem hp) in hs.
have hd : distinguished L (Sub (val s) hp) = distinguished L (1 : [subg (val P)]).
  rewrite hs distinguished_one; reflexivity.
have he := @distinguished_injective S F L P _ _ hd.
have hv := congr1 (fun x : [subg (val P)] => val x) he.
apply val_inj; exact hv.
Qed.

Theorem normalizer_morphism_injm : 'injm normalizer_morphism.
Proof.
apply/subsetP=> s hs; apply/set1P; apply: normalizer_map_kernel.
have hS : s \in [set: N] by rewrite inE.
have he := elimT (kerP normalizer_morphism hS) hs.
exact: he.
Qed.

Theorem normalizer_map_injective : injective normalizer_map.
Proof.
move=> s t he.
have hS : s \in [set: N] by rewrite inE.
have hT : t \in [set: N] by rewrite inE.
have hi := elimT injmP normalizer_morphism_injm.
exact (hi s t hS hT he).
Qed.

End Normalizer.
End DPNormalizerChainTransporter.

Print Assumptions DPNormalizerChainTransporter.normalizer_map_injective.

