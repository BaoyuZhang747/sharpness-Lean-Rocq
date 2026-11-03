(** Native cohomology of the genuine chosen chain automorphism group is
    the actual right-Kan value, with literal subgroup restriction components. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits CategoryModuleExactness
  CategoryModuleRightKan HomologicalModuleIso FusionSystems FusionOrbit FusionSaturation
  PrimeLocalRing PrimeLocalUniversal PrimeLocalModules FusionCentricAcyclicity.
From DiazParkV16b Require Import LinkingSystem LinkingChainAutomorphisms
  ChainNormalizerFusionOrbit ChainNormalizerCohomologyCoefficient
  ChainNormalizerCohomologyLimit ChainNormalizerCohomologyLimitSylow
  GroupCohomologyBase GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  NormalizerChainIndexCategory NormalizerOrbitPairProjection
  NormalizerProjectionCommaRepresentatives NormalizerProjectionCommaStructured
  NormalizerProjectionCommaStructuredLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPLinkingChainAutomorphisms
  DPNormalizerChainIndex DPNormalizerProjectionCommaRepresentatives
  DPNormalizerProjectionCommaStructured DPNormalizerProjectionCommaStructuredLimits
  DPChainNormalizerCohomologyLimit DPChainNormalizerCohomologyLimitSylow
  DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerProjectionCommaGroupLimit.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable d : index_object F.
Local Notation c := (@index_representative S F L p hS sat d).
Local Notation hs := (@index_representative_sylow S F L p hS sat d).
Local Notation proj := (DPNormalizerOrbitPairProjection.projection F).

Definition native_ran_coefficient (R : comPzRingType) (A : lmodType R) n :=
  fobj (module_ran R (functor_op proj))
    (@pair_coefficient S F R (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)).

Definition primes_inverted_ran_value_iso (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n : @isomorphism (module_category R)
  (DPGroupCohomology.value R (chain_automorphism_group L c) A n)
  (fobj (native_ran_coefficient A n) d) :=
  module_iso_comp (@primes_inverted_collection_limit_iso S F L p hS sat c hs hp R localR A n)
    (iso_symm (@structured_collection_limit_iso S F L p hS sat d R
      (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n))).

Theorem primes_inverted_ran_value_component (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n (P : DPChainNormalizerFusionOrbit.collection_category L c) z :
  module_limit_val (module_hom_fun (iso_hom (primes_inverted_ran_value_iso hp localR A n)) z)
    (@collection_point S F L p hS sat d P) =
  module_hom_fun (DPGroupCohomologyPullback.pull A (@collection_group_hom S F L c P) n) z.
Proof.
pose e := @structured_collection_limit_iso S F L p hS sat d R
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n).
pose y := module_hom_fun (iso_hom
  (@primes_inverted_collection_limit_iso S F L p hS sat c hs hp R localR A n)) z.
have he := @structured_collection_limit_component S F L p hS sat d R
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)
  (module_hom_fun (iso_inv e) y) P.
change (module_limit_val (module_hom_fun (iso_hom e)
  (module_hom_fun (iso_inv e) y)) P =
  module_limit_val (module_hom_fun (iso_inv e) y) (@collection_point S F L p hS sat d P)) in he.
rewrite module_iso_inv_hom_apply in he.
change (module_limit_val (module_hom_fun (iso_inv e) y) (@collection_point S F L p hS sat d P) =
  module_hom_fun (DPGroupCohomologyPullback.pull A (@collection_group_hom S F L c P) n) z).
rewrite -he.
exact (@primes_inverted_collection_limit_iso_component S F L p hS sat c hs hp R localR A n P z).
Qed.

Definition field_ran_value_iso (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n :=
  primes_inverted_ran_value_iso (pcharf_prime charp)
    (@DPFusionCentricAcyclicity.field_local p K charp) A n.

Definition prime_local_algebra_ran_value_iso (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n :=
  primes_inverted_ran_value_iso hp
    (DPPrimeLocalModules.scalar_map_implies_primes_inverted hp phi) A n.

Theorem field_ran_value_component (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n (P : DPChainNormalizerFusionOrbit.collection_category L c) z :
  module_limit_val (module_hom_fun (iso_hom (field_ran_value_iso charp A n)) z)
    (@collection_point S F L p hS sat d P) =
  module_hom_fun (DPGroupCohomologyPullback.pull A (@collection_group_hom S F L c P) n) z.
Proof. exact: primes_inverted_ran_value_component. Qed.

Theorem prime_local_algebra_ran_value_component (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n (P : DPChainNormalizerFusionOrbit.collection_category L c) z :
  module_limit_val (module_hom_fun (iso_hom (prime_local_algebra_ran_value_iso hp phi A n)) z)
    (@collection_point S F L p hS sat d P) =
  module_hom_fun (DPGroupCohomologyPullback.pull A (@collection_group_hom S F L c P) n) z.
Proof. exact: primes_inverted_ran_value_component. Qed.
End Comparison.
End DPNormalizerProjectionCommaGroupLimit.
