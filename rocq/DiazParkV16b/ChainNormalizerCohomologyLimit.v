(** Ordinary cohomology of the actual chain automorphism group is the local
    normalizer-collection limit. Every component is the actual restriction. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  CategoryModuleLimitFunctor CategoryModuleExactness HomologicalDiagramLimits HomologicalModuleIso
  CategoryDerivedLimits CategoryDerivedDegreeZero FusionSystems FusionOrbit FusionSaturation
  FusionCentralizerMaps PrimeLocalRing PrimeLocalUniversal PrimeLocalModules FusionCentricAcyclicity.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainNormalizer NormalizerChainEmbedding ChainNormalizerFusionModel
  ChainNormalizerFusionOrbit ChainNormalizerFusionCollection ChainNormalizerCollectionLimit
  ChainNormalizerCohomologyCoefficient GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyOrbitCoefficient GroupCohomologyEmbeddingDiagramBase
  GroupCohomologyEmbeddingCentricLimit GroupCohomologyStableElementsSylow
  FiniteGroupFusionEmbeddingImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChain DPNormalizerChainEmbedding DPChainNormalizerFusionModel
  DPChainNormalizerFusionOrbit DPChainNormalizerCohomologyCoefficient
  DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyEmbeddingDiagramBase DPGroupCohomologyEmbeddingCentricLimit
  DPGroupCohomologyStableElementsSylow DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPChainNormalizerCohomologyLimit.
Section Limit.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable hs : p.-Sylow([set: chain_automorphism_group L c]) (normalizer_image L c).
Local Notation N := [the finGroupType of [subg (normalizer c)]%type].
Local Notation H := (local_system L c).
Local Notation X := (collection_category L c).
Local Notation emb := (normalizer_embedding_morphism L c).
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation D := (DPGroupCohomologyOrbitCoefficient.centric_coefficient H A n).
Local Notation B := (@ambient_coefficient S F L c p sat R A n).
Local Notation I := (@local_coefficient S F L c p sat R A n).

Definition collection_group_hom (P : X) :
    {morphism [set: [subg (DPFusionSubgroup.ambient (val P))]] >-> chain_automorphism_group L c} :=
  group_hom_comp (subgroup_image_inverse (injm_sgval (normalizer c)) (val P))
    (embedding_subgroup_hom emb (val P)).

Lemma collection_group_hom_value (P : X) (x : [subg (DPFusionSubgroup.ambient (val P))]) :
  collection_group_hom P x = emb (subg (normalizer c) (val x)).
Proof.
change (emb (invm (injm_sgval (normalizer c)) (val x)) = emb (subg (normalizer c) (val x))).
apply (f_equal emb); apply val_inj.
have hx := @DPFusionSubgroup.ambient_subgK S (normalizer c) (val P) (val x) (valP x).
rewrite hx.
exact (@DPFiniteGroupFusionEmbeddingImage.ambient_inverseK N S
  [morphism of @sgval S (normalizer c)] (injm_sgval (normalizer c)) (val P) (val x) (valP x)).
Qed.

Definition collection_limit_coefficient_iso : @isomorphism (module_category R)
    (module_limit_type I) (module_limit_type B) :=
  functor_iso (module_limit_functor R (opposite X))
    (@collection_coefficient_nat_iso S F L c p sat R A n).

Lemma collection_limit_coefficient_component (v : module_limit_type I) (P : X) :
  module_limit_val (module_hom_fun (iso_hom collection_limit_coefficient_iso) v) P =
    module_hom_fun (pull A (subgroup_image_inverse (injm_sgval (normalizer c)) (val P)) n)
      (module_limit_val v P).
Proof.
change (module_limit_val
  (limit_action (iso_hom (@collection_coefficient_nat_iso S F L c p sat R A n)) v) P =
  module_hom_fun (pull A (subgroup_image_inverse (injm_sgval (normalizer c)) (val P)) n)
    (module_limit_val v P)).
by rewrite limit_action_coordinate collection_coefficient_nat_iso_hom.
Qed.

Variable u : R.
Variable hu : u * (indexg [set: chain_automorphism_group L c] (normalizer_image L c))%:R = 1.

Definition native_collection_limit_iso : @isomorphism (module_category R)
    (value R (chain_automorphism_group L c) A n) (module_limit_type B) :=
  module_iso_comp (@embedding_centric_limit_iso N (chain_automorphism_group L c) emb
    (local_embedding_faithful L c) R A n p hs u hu)
    (module_iso_comp (@DPChainNormalizerCollectionLimit.sylow_collection_limit_iso
      S F L c p hS sat hs R D) collection_limit_coefficient_iso).

Theorem native_collection_limit_iso_component (P : X) z :
  module_limit_val (module_hom_fun (iso_hom native_collection_limit_iso) z) P =
    module_hom_fun (pull A (collection_group_hom P) n) z.
Proof.
change (module_limit_val (module_hom_fun (iso_hom collection_limit_coefficient_iso)
  (module_hom_fun (iso_hom (@DPChainNormalizerCollectionLimit.sylow_collection_limit_iso
    S F L c p hS sat hs R D))
    (module_hom_fun (iso_hom (@embedding_centric_limit_iso N (chain_automorphism_group L c) emb
      (local_embedding_faithful L c) R A n p hs u hu)) z))) P =
  module_hom_fun (pull A (collection_group_hom P) n) z).
rewrite collection_limit_coefficient_component
  DPChainNormalizerCollectionLimit.sylow_collection_limit_component
  embedding_centric_limit_iso_component.
rewrite /collection_group_hom !pull_composition; reflexivity.
Qed.

Definition native_collection_derived_zero_iso : @isomorphism (module_category R)
    (value R (chain_automorphism_group L c) A n) (derived_limit R B 0%N) :=
  module_iso_comp native_collection_limit_iso (iso_symm (derived_degree_zero_iso R B)).

Theorem native_collection_derived_zero_iso_component (P : X) z :
  module_limit_val (module_hom_fun (iso_hom (derived_degree_zero_iso R B))
    (module_hom_fun (iso_hom native_collection_derived_zero_iso) z)) P =
      module_hom_fun (pull A (collection_group_hom P) n) z.
Proof.
change (module_limit_val (module_hom_fun (iso_hom (derived_degree_zero_iso R B))
  (module_hom_fun (iso_inv (derived_degree_zero_iso R B))
    (module_hom_fun (iso_hom native_collection_limit_iso) z))) P =
  module_hom_fun (pull A (collection_group_hom P) n) z).
rewrite module_iso_inv_hom_apply; exact: native_collection_limit_iso_component.
Qed.
End Limit.
End DPChainNormalizerCohomologyLimit.
