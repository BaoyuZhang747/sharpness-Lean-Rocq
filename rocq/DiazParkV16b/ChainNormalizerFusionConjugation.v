(** Conjugation in the actual chain automorphism group yields a literal
    chain-preserving extension over the minimal top join. *)
From mathcomp Require Import all_boot all_fingroup.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingSystemAutomorphisms
  LinkingChainObjects LinkingChainAutomorphisms NormalizerChainNormalizer
  NormalizerChainTransporter NormalizerChainEmbedding
  LinkingChainAutomorphismStabilizer LinkingSystemNormalizerExtension
  LinkingSystemNormalizerActionRange LinkingSystemNormalizerProjection
  ChainNormalizerFusionExtension ChainNormalizerFusionForward.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPCentricLinking DPLinkingAutomorphisms DPLinkingChains
  DPLinkingChainAutomorphisms DPNormalizerChain DPNormalizerChainTransporter
  DPNormalizerChainEmbedding DPLinkingChainStabilizer DPLinkingNormalizerExtension
  DPLinkingNormalizerActionRange DPLinkingNormalizerProjection
  DPChainNormalizerFusion DPChainNormalizerFusionForward.
Local Open Scope group_scope.

Module DPChainNormalizerFusionConjugation.
Section Conjugation.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variables P Q : {group S}.
Hypotheses (hP : P \subset normalizer c) (hQ : Q \subset normalizer c).
Variable f : DPFusion.map P Q.
Variable g : chain_automorphism_group L c.
Hypothesis conjugates : forall x : [subg P],
  normalizer_embedding L (target_element hQ f x) =
    normalizer_embedding L (source_element hP x) ^ g.
Local Notation U := (top c).
Local Notation JP := (join_object c P).
Local Notation JQ := (join_object c Q).
Local Notation a := (projection ord_max g).
Local Notation hPN := (subset_trans hP (normalizer_sub_top c)).
Local Notation hJN := (join_normalizes_top hP).
Local Notation hKN := (join_normalizes_top hQ).

Definition target_join_element (x : [subg P]) : [subg (join_subgroup c Q)] :=
  Sub (f (val x)) (subsetP (acting_sub_join c Q) _ (DPFusion.map_into f (valP x))).

Lemma chain_conjugation_top (x : [subg P]) :
  coordinate L (target_element hQ f x) ord_max =
    coordinate L (source_element hP x) ord_max ^ a.
Proof.
have he := congr1 (top_morphism L c) (conjugates x).
rewrite morphJ ?inE // in he.
change (projection ord_max (normalizer_embedding L (target_element hQ f x)) =
  projection ord_max (normalizer_embedding L (source_element hP x)) ^ a) in he.
by rewrite !normalizer_embedding_projection in he.
Qed.

Lemma source_action_coordinate (x : [subg P]) :
  normalizer_action L hPN x = coordinate L (source_element hP x) ord_max.
Proof.
rewrite /normalizer_action /coordinate; congr (normalizer_map L _); apply val_inj; reflexivity.
Qed.

Lemma target_action_coordinate (x : [subg P]) :
  normalizer_action L hKN (target_join_element x) = coordinate L (target_element hQ f x) ord_max.
Proof.
rewrite /normalizer_action /coordinate; congr (normalizer_map L _); apply val_inj; reflexivity.
Qed.

Lemma source_join_action (x : [subg P]) :
  normalizer_action L hJN (source_join_element c x) = normalizer_action L hPN x.
Proof. apply: normalizer_action_eq; reflexivity. Qed.

Lemma acting_range (x : [subg P]) :
  normalizer_action L hKN (target_join_element x) = normalizer_action L hPN x ^ a.
Proof. rewrite source_action_coordinate target_action_coordinate; exact: chain_conjugation_top. Qed.

Lemma join_range : forall x : [subg (val JP)], exists y : [subg (val JQ)],
  @target_action S F L U JQ hKN y = @source_action S F L U JP hJN x ^ a.
Proof.
move=> x.
have hr : forall z : [subg P], exists y : [subg (val JQ)],
    normalizer_action L hKN y = normalizer_action L hPN z ^ a.
  move=> z; exists (target_join_element z); exact: acting_range.
have [y hy] := @join_action_range S F L U P JQ hPN (top_sub_join c Q) hKN a hr x.
exists y.
change (normalizer_action L hKN y = normalizer_action L hJN x ^ a).
rewrite hy; congr (_ ^ a); apply: normalizer_action_eq; reflexivity.
Qed.

Theorem chain_conjugation_induces_extension p (sat : DPFusionSaturation.saturated F p) :
  normalizer_extension c f.
Proof.
have [b hb] := @exists_linking_normalizer_extension S F L U JP JQ
  (top_sub_join c P) (top_sub_join c Q) hJN hKN a join_range p sat.
apply/normalizer_extensionP; exists (val (linking_projection L b)); split; first exact: valP.
split.
- move=> i.
  refine (@extension_projection_image S F L U JP JQ (top_sub_join c P)
    (top_sub_join c Q) a b hb (subgroup c i) (@entry_sub_top S F c i)
    (@entry_sub_join S F c P i) _).
  move=> x hx.
  change (DPFusion.map_fun (val (linking_projection L (top_morphism L c g))) x \in subgroup c i).
  rewrite (top_projection_action g hx); exact: DPFusion.map_into.
- move=> x hx.
  have he := @extension_matches_action S F L U JP JQ (top_sub_join c P)
    (top_sub_join c Q) hJN hKN a b hb (source_join_element c (Sub x hx))
    (target_join_element (Sub x hx)).
  apply he.
  change (normalizer_action L hKN (target_join_element (Sub x hx)) =
    normalizer_action L hJN (source_join_element c (Sub x hx)) ^ a).
  rewrite source_join_action; exact: acting_range.
Qed.
End Conjugation.

Section Equivalence.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variables P Q : {group S}.
Hypotheses (hP : P \subset normalizer c) (hQ : Q \subset normalizer c).
Variable f : DPFusion.map P Q.
Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.

Theorem normalizer_extension_iff_chain_conjugation :
  normalizer_extension c f <-> exists g : chain_automorphism_group L c,
    forall x : [subg P], normalizer_embedding L (target_element hQ f x) =
      normalizer_embedding L (source_element hP x) ^ g.
Proof.
split.
- exact: extension_induces_chain_conjugation.
- move=> [g hg]; exact: (@chain_conjugation_induces_extension S F L c P Q hP hQ f g hg p sat).
Qed.
End Equivalence.
End DPChainNormalizerFusionConjugation.

Check DPChainNormalizerFusionConjugation.normalizer_extension_iff_chain_conjugation.
Print Assumptions DPChainNormalizerFusionConjugation.chain_conjugation_induces_extension.
Print Assumptions DPChainNormalizerFusionConjugation.normalizer_extension_iff_chain_conjugation.
