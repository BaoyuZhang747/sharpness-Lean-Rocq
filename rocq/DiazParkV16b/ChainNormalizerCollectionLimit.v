(** Actual limit restriction to the literal chain-normalizer collection,
    normalized at every object. All collection hypotheses are discharged. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  CategoryLimitMaps CategoryAdjunction CategoryIsomorphism CategoryIsomorphismAdjunction
  HomologicalModuleIso FusionSystems FusionOrbit FusionSaturation FusionCollectionAcyclicity.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainNormalizer NormalizerChainEmbedding ChainNormalizerFusionModel
  ChainNormalizerFusionOrbit ChainNormalizerBottomCollection ChainNormalizerFusionSaturation
  ChainNormalizerFusionCollectionAdapter FusionCollectionLimitRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPLinkingChains DPLinkingChainAutomorphisms DPNormalizerChain
  DPNormalizerChainEmbedding DPChainNormalizerFusionModel DPChainNormalizerFusionOrbit
  DPChainNormalizerFusionCollectionAdapter DiazParkHomologicalModuleIso.
Local Open Scope group_scope.

Module DPChainNormalizerCollectionLimit.
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
Local Notation C := (fun P : {group N} => is_true (@ambient_centric S F c P)).
Variable R : pzRingType.
Variable D : module_codiagram R (centric_orbit_category H).
Local Notation E := (fobj (DPFusionCollectionAcyclicity.collection_restriction H C R) D).

Definition literal_limit_adapter : @isomorphism (module_category R)
    (module_limit_type E)
    (module_limit_type (@literal_restriction S F L c p sat R D)) :=
  left_adjoint_limit_iso
    (adjunction_op (category_iso_adjunction (category_iso_symm
      (@collection_category_iso S F L c p sat)))) E (module_limit E)
    (module_limit (@literal_restriction S F L c p sat R D)).

Lemma literal_limit_adapter_component (v : module_limit_type E) (P : collection_category L c) :
  module_limit_val (module_hom_fun (iso_hom literal_limit_adapter) v) P =
    module_limit_val v (@to_prop_object S F L c p sat P).
Proof.
have he := @left_adjoint_limit_iso_hom _ _ _ _ _
  (adjunction_op (category_iso_adjunction (category_iso_symm
    (@collection_category_iso S F L c p sat)))) E (module_limit E)
  (module_limit (@literal_restriction S F L c p sat R D)).
rewrite /literal_limit_adapter he.
have hf := @limit_restrict_map_fac _ _ _
  (functor_op (@to_prop S F L c p sat)) E (module_limit E)
  (module_limit (@literal_restriction S F L c p sat R D)) P.
exact (congr1 (fun f => module_hom_fun f v) hf).
Qed.

Definition sylow_collection_limit_iso : @isomorphism (module_category R)
    (module_limit_type D) (module_limit_type (@literal_restriction S F L c p sat R D)) :=
  module_iso_comp
    (@DPFusionCollectionLimitRestriction.sufficient_collection_limit_iso N H p
      (@DPChainNormalizerBottomCollection.normalizer_carrier_pgroup S F c p hS)
      (@DPChainNormalizerFusionSaturation.local_saturated S F L c p hs) C
      (@ambient_centric_conjugate S F L c p sat) (@ambient_centric_overgroup S F c)
      (@DPChainNormalizerBottomCollection.centric_radical_ambient_centric S F L c p hS) R D)
    literal_limit_adapter.

Theorem sylow_collection_limit_component (v : module_limit_type D)
    (P : collection_category L c) :
  module_limit_val (module_hom_fun (iso_hom sylow_collection_limit_iso) v) P =
    module_limit_val v (@collection_local_object S F L c p sat P).
Proof.
change (module_limit_val (module_hom_fun (iso_hom literal_limit_adapter)
  (module_hom_fun (iso_hom
    (@DPFusionCollectionLimitRestriction.sufficient_collection_limit_iso N H p
      (@DPChainNormalizerBottomCollection.normalizer_carrier_pgroup S F c p hS)
      (@DPChainNormalizerFusionSaturation.local_saturated S F L c p hs) C
      (@ambient_centric_conjugate S F L c p sat) (@ambient_centric_overgroup S F c)
      (@DPChainNormalizerBottomCollection.centric_radical_ambient_centric S F L c p hS) R D)) v)) P =
  module_limit_val v (@collection_local_object S F L c p sat P)).
rewrite literal_limit_adapter_component.
exact: DPFusionCollectionLimitRestriction.sufficient_collection_limit_component.
Qed.

End Limit.
End DPChainNormalizerCollectionLimit.
