(** The actual first-entry functor from pointed normalizer chains to pointed
    normalized centric subgroups.  Its arrows retain genuine extensions. *)
From mathcomp Require Import all_boot all_fingroup boolp.
From DiazPark Require Import Category CategoryComma FusionMaps FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingChainObjects NormalizerChainIndices
  NormalizerChainExtensions NormalizerChainNormalizer NormalizerOrbitPairCategory
  NormalizerOrbitCommaImageObjects NormalizerPointedSubgroupExtensions NormalizerPointedSubgroups.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionOrbit DPLinkingChains.
Local Open Scope group_scope.

Module DPNormalizerOrbitPointedFirst.
Section First.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable P : centric_object F.
Local Notation CP := (DPNormalizerOrbitCommaImage.pointed_category P).
Local Notation SP := (DPNormalizerPointedSubgroups.pointed_category P).

Definition first_object (A : CP) : SP.
Proof.
pose X := DPNormalizerOrbitCommaImage.pointed_pair A.
refine (@DPNormalizerPointedSubgroups.Build_object S F P
  (DPNormalizerOrbitPair.acting X) (DPNormalizerOrbitCommaImage.pointed_iso A)
  (val (bottom (DPNormalizerOrbitPair.chain_of X))) (valP _) _).
exact (subset_trans (DPNormalizerOrbitPair.acting_normalizes X)
  (@DPNormalizerChain.normalizer_sub S F (DPNormalizerOrbitPair.chain_of X) ord0)).
Defined.

Lemma first_map (A B : CP) (f : hom CP A B) :
  hom SP (first_object A) (first_object B).
Proof.
change (DPNormalizerPointedSubgroups.related (first_object A) (first_object B)).
have [g [hg [a]]] := DPNormalizerOrbitPair.hom_compatible (costructured_map f).
exists g; split.
- have hf := costructured_commutes f.
  change (Category.compose (iso_hom (DPNormalizerOrbitCommaImage.pointed_iso A))
    (val (costructured_map f)) = iso_hom (DPNormalizerOrbitCommaImage.pointed_iso B)) in hf.
  by rewrite hg.
- constructor.
  pose c := DPNormalizerOrbitPair.chain_of (DPNormalizerOrbitCommaImage.pointed_pair A).
  pose d := DPNormalizerOrbitPair.chain_of (DPNormalizerOrbitCommaImage.pointed_pair B).
  have hc : val (bottom c) \subset DPNormalizerChainExtensions.carrier a.
    apply: subset_trans (DPNormalizerChainExtensions.entry_sub_carrier a ord0).
    exact (@entry_mono S F c ord0 _ (leq0n _)).
  refine (@DPNormalizerSubgroupExtensions.Build_extension S F (val (bottom c))
    (val (bottom d)) _ _ (val g) (DPNormalizerChainExtensions.carrier a)
    (DPNormalizerChainExtensions.acting_sub a) hc
    (DPNormalizerChainExtensions.extension_map a)
    (DPNormalizerChainExtensions.extension_allowed a)
    (DPNormalizerChainExtensions.on_acting a) _).
  move=> x hx.
  have hs : x \in subgroup c (DPNormalizerChainIndices.index
      (DPNormalizerChainExtensions.indices a) ord0) :=
    subsetP (@entry_mono S F c ord0 _ (leq0n _)) _ hx.
  change (DPNormalizerChainExtensions.extension_map a x \in subgroup d ord0).
  rewrite -(DPNormalizerChainExtensions.entry_images a ord0).
  exact: mem_morphim (subsetP hc _ hx) hs.
Qed.

Definition first_functor : functor CP SP.
Proof.
refine (@Build_functor CP SP first_object (@first_map) _ _);
  intros; apply DPNormalizerPointedSubgroups.hom_unique.
Defined.
End First.
End DPNormalizerOrbitPointedFirst.
