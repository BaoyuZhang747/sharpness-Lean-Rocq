(** Every literal chain-preserving join extension is induced by conjugation
    in the actual compatible linking-chain automorphism group. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainNormalizer
  NormalizerChainTransporter NormalizerChainEmbedding LinkingSystemNormalizerSquares
  ChainNormalizerFusionExtension ChainNormalizerFusionLift.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPCentricLinking DPLinkingAutomorphisms DPLinkingChains
  DPLinkingChainAutomorphisms DPNormalizerChain DPNormalizerChainTransporter
  DPNormalizerChainEmbedding DPChainNormalizerFusion DPChainNormalizerFusionLift.
Local Open Scope group_scope.

Module DPChainNormalizerFusionForward.
Section Forward.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variables P Q : {group S}.
Hypotheses (hP : P \subset normalizer c) (hQ : Q \subset normalizer c).
Variable f : DPFusion.map P Q.

Definition source_element (x : [subg P]) : [subg (normalizer c)] :=
  Sub (val x) (subsetP hP _ (valP x)).
Definition target_element (x : [subg P]) : [subg (normalizer c)] :=
  Sub (f (val x)) (subsetP hQ _ (DPFusion.map_into f (valP x))).
Definition source_join_element (x : [subg P]) : [subg (join_subgroup c P)] :=
  Sub (val x) (subsetP (acting_sub_join c P) _ (valP x)).

Section Witness.
Variable b : DPFusion.map (join_subgroup c P) (join_subgroup c Q).
Hypothesis hb : DPFusionSystem.allowed F b.
Hypothesis hc : @preserves_chain S F c P Q b.
Hypothesis hbf : {in P, b =1 f}.
Local Notation a := (@top_action S F L c P Q b hb hc).
Local Notation B := (@extension_lift S F L c P Q b hb).
Local Notation g := (@chain_action S F L c P Q b hb hc).

Lemma extension_top_conjugation (x : [subg P]) :
  coordinate L (target_element x) ord_max = coordinate L (source_element x) ord_max ^ a.
Proof.
have ht := @DPLinkingNormalizerSquares.extension_conjugation S F L
  (top c) (join_object c P) (join_object c Q)
  (top_sub_join c P) (top_sub_join c Q) (join_normalizes_top hP) (join_normalizes_top hQ)
  a B (@top_action_square S F L c P Q b hb hc) (source_join_element x).
have hs : @DPLinkingNormalizerSquares.source_normalizer S F (top c) (join_object c P)
    (join_normalizes_top hP) (source_join_element x) = coordinate_normalizer (source_element x) ord_max.
  apply val_inj; reflexivity.
have hd : @DPLinkingNormalizerSquares.target_normalizer S F L (top c) (join_object c P)
    (join_object c Q) (join_normalizes_top hQ) B (source_join_element x) =
    coordinate_normalizer (target_element x) ord_max.
  apply val_inj.
  change (DPFusion.map_fun (val (linking_projection L B)) (val x) = f (val x)).
  rewrite extension_lift_projection; exact: hbf (valP x).
rewrite hs hd in ht; exact ht.
Qed.

Theorem witness_induces_conjugation (x : [subg P]) :
  normalizer_embedding L (target_element x) = normalizer_embedding L (source_element x) ^ g.
Proof.
refine (@top_projection_injective S F L c
  (normalizer_embedding L (target_element x))
  (normalizer_embedding L (source_element x) ^ g) _).
have hp : projection ord_max (normalizer_embedding L (source_element x) ^ g) =
  projection ord_max (normalizer_embedding L (source_element x)) ^ projection ord_max g.
  change (projection_morphism L ord_max (normalizer_embedding L (source_element x) ^ g) =
    projection_morphism L ord_max (normalizer_embedding L (source_element x)) ^ projection_morphism L ord_max g).
  by rewrite morphJ ?inE.
rewrite hp !normalizer_embedding_projection chain_action_top.
exact: extension_top_conjugation.
Qed.
End Witness.

Theorem extension_induces_chain_conjugation : normalizer_extension c f ->
  exists g : chain_automorphism_group L c,
    forall x : [subg P], normalizer_embedding L (target_element x) =
      normalizer_embedding L (source_element x) ^ g.
Proof.
move/normalizer_extensionP=> [b [hb [hc hbf]]].
have hc' : @preserves_chain S F c P Q b by apply/preserves_chainP.
exists (@chain_action S F L c P Q b hb hc'); move=> x.
exact (@witness_induces_conjugation b hb hc' hbf x).
Qed.

End Forward.
End DPChainNormalizerFusionForward.
