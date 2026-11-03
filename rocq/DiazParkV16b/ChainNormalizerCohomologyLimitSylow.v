(** The coefficient hypotheses of the manuscript construct the scalar needed
    by the actual chain-normalizer restriction comparison. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits CategoryDerivedLimits
  CategoryDerivedDegreeZero FusionSystems FusionSaturation PrimeLocalRing PrimeLocalUniversal
  PrimeLocalModules FusionCentricAcyclicity.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainEmbedding ChainNormalizerFusionOrbit ChainNormalizerFusionCollection
  ChainNormalizerCohomologyCoefficient ChainNormalizerCohomologyLimit
  GroupCohomologyPullback GroupCohomologyStableElementsSylow.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPLinkingChains DPLinkingChainAutomorphisms
  DPNormalizerChainEmbedding DPChainNormalizerFusionOrbit DPChainNormalizerFusionCollection
  DPChainNormalizerCohomologyCoefficient DPChainNormalizerCohomologyLimit
  DPGroupCohomologyPullback DPGroupCohomologyStableElementsSylow.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPChainNormalizerCohomologyLimitSylow.
Section Sylow.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable c : chain F.
Variable hs : p.-Sylow([set: chain_automorphism_group L c]) (normalizer_image L c).

Definition primes_inverted_collection_limit_iso (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n :=
  @native_collection_limit_iso S F L c p hS sat hs R A n
    (@sylow_index_inverse (chain_automorphism_group L c) (normalizer_image L c) p hp hs R localR)
    (@sylow_index_inverse_spec (chain_automorphism_group L c) (normalizer_image L c) p hp hs R localR).

Definition field_collection_limit_iso (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n :=
  primes_inverted_collection_limit_iso (pcharf_prime charp)
    (@DPFusionCentricAcyclicity.field_local p K charp) A n.

Definition prime_local_algebra_collection_limit_iso (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n :=
  primes_inverted_collection_limit_iso hp
    (DPPrimeLocalModules.scalar_map_implies_primes_inverted hp phi) A n.

Theorem primes_inverted_collection_limit_iso_component (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n (P : collection_category L c) z :
  module_limit_val (module_hom_fun
    (iso_hom (primes_inverted_collection_limit_iso hp localR A n)) z) P =
      module_hom_fun (pull A (@collection_group_hom S F L c P) n) z.
Proof. exact: native_collection_limit_iso_component. Qed.

Theorem field_collection_limit_iso_component (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n (P : collection_category L c) z :
  module_limit_val (module_hom_fun (iso_hom (field_collection_limit_iso charp A n)) z) P =
    module_hom_fun (pull A (@collection_group_hom S F L c P) n) z.
Proof. exact: native_collection_limit_iso_component. Qed.

Theorem prime_local_algebra_collection_limit_iso_component (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n (P : collection_category L c) z :
  module_limit_val (module_hom_fun
    (iso_hom (prime_local_algebra_collection_limit_iso hp phi A n)) z) P =
      module_hom_fun (pull A (@collection_group_hom S F L c P) n) z.
Proof. exact: native_collection_limit_iso_component. Qed.

Definition field_collection_derived_zero_iso (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n :=
  @native_collection_derived_zero_iso S F L c p hS sat hs K A n
    (@sylow_index_inverse (chain_automorphism_group L c) (normalizer_image L c) p
      (pcharf_prime charp) hs K (@DPFusionCentricAcyclicity.field_local p K charp))
    (@sylow_index_inverse_spec (chain_automorphism_group L c) (normalizer_image L c) p
      (pcharf_prime charp) hs K (@DPFusionCentricAcyclicity.field_local p K charp)).

Theorem field_collection_derived_zero_iso_component (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n (P : collection_category L c) z :
  module_limit_val (module_hom_fun (iso_hom (derived_degree_zero_iso K
    (@ambient_coefficient S F L c p sat K A n)))
    (module_hom_fun (iso_hom (field_collection_derived_zero_iso charp A n)) z)) P =
      module_hom_fun (pull A (@collection_group_hom S F L c P) n) z.
Proof. exact: native_collection_derived_zero_iso_component. Qed.

Definition prime_local_algebra_collection_derived_zero_iso (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n :=
  @native_collection_derived_zero_iso S F L c p hS sat hs R A n
    (@sylow_index_inverse (chain_automorphism_group L c) (normalizer_image L c) p
      hp hs R (DPPrimeLocalModules.scalar_map_implies_primes_inverted hp phi))
    (@sylow_index_inverse_spec (chain_automorphism_group L c) (normalizer_image L c) p
      hp hs R (DPPrimeLocalModules.scalar_map_implies_primes_inverted hp phi)).

Theorem prime_local_algebra_collection_derived_zero_iso_component (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n (P : collection_category L c) z :
  module_limit_val (module_hom_fun (iso_hom (derived_degree_zero_iso R
    (@ambient_coefficient S F L c p sat R A n)))
    (module_hom_fun (iso_hom (prime_local_algebra_collection_derived_zero_iso hp phi A n)) z)) P =
      module_hom_fun (pull A (@collection_group_hom S F L c P) n) z.
Proof. exact: native_collection_derived_zero_iso_component. Qed.
End Sylow.

Definition field_representative_collection_limit_iso
    (S : finGroupType) (F : DPFusionSystem.system S) (L : DPCentricLinking.system F)
    (p : nat) (hS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (c : chain F) (K : fieldType) (charp : p \in [pchar K]) (A : lmodType K) n :=
  @field_collection_limit_iso S F L p hS sat (@sylow_representative S F L p hS sat c)
    (@representative_sylow S F L p hS sat c) K charp A n.

Definition prime_local_algebra_representative_collection_limit_iso
    (S : finGroupType) (F : DPFusionSystem.system S) (L : DPCentricLinking.system F)
    (p : nat) (hp : prime p) (hS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (c : chain F) (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n :=
  @prime_local_algebra_collection_limit_iso S F L p hS sat (@sylow_representative S F L p hS sat c)
    (@representative_sylow S F L p hS sat c) hp R phi A n.
End DPChainNormalizerCohomologyLimitSylow.
