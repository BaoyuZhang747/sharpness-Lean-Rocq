(** The actual local fusion system on the simultaneous normalizer, induced
    through its proved faithful embedding into the chain automorphism group. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionCentralizerMaps.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainNormalizer
  NormalizerChainEmbedding FiniteGroupFusionEmbedding ChainNormalizerFusionExtension
  ChainNormalizerFusionForward ChainNormalizerFusionConjugation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionSubgroup DPLinkingChains DPNormalizerChain
  DPNormalizerChainEmbedding DPChainNormalizerFusion DPChainNormalizerFusionForward
  DPChainNormalizerFusionConjugation.
Local Open Scope group_scope.

Module DPChainNormalizerFusionModel.
Section Model.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Local Notation N := [the finGroupType of [subg (normalizer c)]%type].

Definition local_system : DPFusionSystem.system N :=
  DPFiniteGroupFusionEmbedding.system (normalizer_embedding_morphism L c).

Theorem local_embedding_faithful : 'injm (normalizer_embedding_morphism L c).
Proof. exact: normalizer_embedding_injm. Qed.

Lemma ambient_source_element (P : {group N}) (x : [subg (ambient P)]) :
  source_element (ambient_sub P) x = subg (normalizer c) (val x).
Proof.
apply val_inj; symmetry; exact: ambient_subgK (valP x).
Qed.

Lemma ambient_target_element (P Q : {group N}) (f : DPFusion.map P Q)
    (x : [subg (ambient P)]) :
  target_element (ambient_sub Q) (lift f) x = f (subg (normalizer c) (val x)).
Proof.
apply val_inj; change (lift f (val x) = val (f (subg (normalizer c) (val x)))).
have hx := ambient_repr (valP x).
have hv := ambient_subgK (valP x).
rewrite -{1}hv; exact: liftE hx.
Qed.

Variable p : nat.
Hypothesis sat : DPFusionSaturation.saturated F p.

Theorem local_allowed_extension (P Q : {group N}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed local_system f = normalizer_extension c (lift f).
Proof.
have hi := @normalizer_extension_iff_chain_conjugation S F L c (ambient P) (ambient Q)
  (ambient_sub P) (ambient_sub Q) (lift f) p sat.
apply/idP/idP.
- move/DPFiniteGroupFusionEmbedding.allowedP=> [g hg].
  apply (proj2 hi); exists g=> x.
  rewrite ambient_source_element ambient_target_element.
  exact: hg (ambient_repr (valP x)).
- move=> hf; have [g hg] := proj1 hi hf.
  apply/DPFiniteGroupFusionEmbedding.allowedP; exists g=> x hx.
  have ht := hg (Sub (val x) (ambient_mem hx)).
  rewrite ambient_source_element ambient_target_element sgvalK in ht.
  exact ht.
Qed.

Theorem local_ambient_allowed (P Q : {group N}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed local_system f -> DPFusionSystem.allowed F (lift f).
Proof.
rewrite local_allowed_extension; exact: normalizer_extension_allowed.
Qed.

End Model.
End DPChainNormalizerFusionModel.
