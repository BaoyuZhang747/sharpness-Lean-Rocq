(** The chosen genuine normalizer Sylow representative has the required
    Sylow fusion stabilizer, and represents the original chain class. *)
From mathcomp Require Import all_boot all_fingroup pgroup center generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  LinkingChainAutomorphismStabilizerEquivalence LinkingChainAutomorphismStabilizerSylow
  NormalizerChainEmbedding NormalizerChainStabilizer NormalizerChainTransport
  NormalizerChainIndices NormalizerChainExtensions NormalizerChainRelations NormalizerChainConjugacy
  NormalizerChainIndexCategory ChainNormalizerFusionCollection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPLinkingChains DPLinkingChainAutomorphisms DPLinkingChainStabilizerEquivalence
  DPLinkingChainNormalizerSylow DPNormalizerChainEmbedding DPNormalizerChainStabilizer
  DPNormalizerChainTransport DPNormalizerChainIndices DPNormalizerChainExtensions
  DPNormalizerChainRelations DPNormalizerChainConjugacy DPNormalizerChainIndex
  DPChainNormalizerFusionCollection.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPNormalizerProjectionCommaRepresentatives.
Section Chain.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable p : nat.
Variable hS : p.-group [set: S].

Lemma normalizer_image_sylow_automizer
    (hs : p.-Sylow([set: chain_automorphism_group L c]) (normalizer_image L c)) :
  p.-Sylow(fusion_stabilizer c)
    (DPFusionSaturation.ambient_aut_group (val (top c)) :&: fusion_stabilizer c).
Proof.
have hZ : p.-nat #|'Z(val (top c))| := pgroupS (subsetT _) hS.
have hh := card_Hall hs.
rewrite normalizer_image_card simultaneous_normalizer_order cardsT chain_automorphism_order
  partnM ?cardG_gt0 // (part_pnat_id hZ) in hh.
apply/pHallP; split; first exact: subsetIr.
apply/eqP; rewrite -(eqn_pmul2l (cardG_gt0 'Z(val (top c))%G)).
exact/eqP.
Qed.

End Chain.
Section ChainRepresentative.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.

Lemma representative_automizer_sylow :
  p.-Sylow(fusion_stabilizer (@sylow_representative S F L p hS sat c))
    (DPFusionSaturation.ambient_aut_group (val (top (@sylow_representative S F L p hS sat c))) :&:
      fusion_stabilizer (@sylow_representative S F L p hS sat c)).
Proof.
exact (@normalizer_image_sylow_automizer S F L
  (@sylow_representative S F L p hS sat c) p hS
  (@representative_sylow S F L p hS sat c)).
Qed.
End ChainRepresentative.

Section TransportClass.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable c : chain F.
Variable Q : {group S}.
Variable f : DPFusion.map (val (top c)) Q.
Variable hf : DPFusionSystem.allowed F f.
Local Notation d := (@transport S F c Q f hf).

Lemma transport_conjugate : conjugate c d.
Proof.
pose e : selector c d := DPNormalizerChainIndices.identity c.
pose g := DPFusion.compose f (inclusion (subsetT Q)).
have hg := DPFusionSystem.composition_closed hf (DPFusionSystem.inclusion_allowed F (subsetT Q)).
have he : forall i, map_morphism g @* subgroup c (index e i) = subgroup d i.
  move=> i; rewrite /e identity_index transport_subgroup.
  apply: eq_morphim=> x hx.
  by rewrite map_morphismE /g compose_in // inclusion_in ?map_into.
have h1 : forall x, x \in 1%G -> g x = DPFusion.identity 1%G x.
  move=> x /set1P ->; by rewrite !map_one.
apply/conjugateP.
exists (@Build_extension S F c d 1%G 1%G (DPFusion.identity 1%G) e
  (val (top c)) (sub1G _) (@entry_sub_top S F c _)
  g hg h1 he).
exists (fun i => i); move=> i; exact: identity_index.
Qed.
End TransportClass.

Section Representatives.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.

Lemma sylow_representative_class (c : chain F) :
  chain_class (@sylow_representative S F L p hS sat c) = chain_class c.
Proof.
apply/class_eq_conjugate; apply: conjugate_reverse.
exact: transport_conjugate.
Qed.

Definition index_representative (d : index_object F) : chain F :=
  @sylow_representative S F L p hS sat (repr d).

Lemma index_representative_class (d : index_object F) : chain_class (index_representative d) = d.
Proof. rewrite /index_representative sylow_representative_class; exact: reprK. Qed.

Lemma index_representative_sylow (d : index_object F) :
  p.-Sylow([set: chain_automorphism_group L (index_representative d)])
    (normalizer_image L (index_representative d)).
Proof. exact: representative_sylow. Qed.

Lemma index_representative_automizer_sylow (d : index_object F) :
  p.-Sylow(fusion_stabilizer (index_representative d))
    (DPFusionSaturation.ambient_aut_group (val (top (index_representative d))) :&:
      fusion_stabilizer (index_representative d)).
Proof. exact: representative_automizer_sylow. Qed.
End Representatives.
End DPNormalizerProjectionCommaRepresentatives.
