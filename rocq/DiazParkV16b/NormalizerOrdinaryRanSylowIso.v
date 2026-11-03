(** The genuine native normalizer diagram, on constructed Sylow chain
    representatives, is naturally isomorphic to the actual right Kan diagram. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLimits
  CategoryModuleExactness CategoryNaturalIso FusionSystems FusionOrbit FusionSaturation
  PrimeLocalRing PrimeLocalUniversal PrimeLocalModules FusionCentricAcyclicity.
From DiazParkV16b Require Import LinkingSystem NormalizerChainIndexCategory
  GroupCohomologyOrbitCoefficient NormalizerOrdinaryCoefficient NormalizerOrdinaryRanMap
  NormalizerOrdinaryRanComponents NormalizerProjectionCommaRepresentatives
  NormalizerProjectionCommaStructuredLimits NormalizerProjectionCommaGroupLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPNormalizerChainIndex
  DPNormalizerOrdinaryCoefficient DPNormalizerOrdinaryRanMap DPNormalizerOrdinaryRanComponents
  DPNormalizerProjectionCommaRepresentatives DPNormalizerProjectionCommaStructuredLimits
  DPNormalizerProjectionCommaGroupLimit.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerOrdinaryRanSylowIso.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Local Notation r := (@index_representative S F L p hS sat).
Local Notation hr := (@index_representative_class S F L p hS sat).

Definition sylow_coefficient (R : comPzRingType) (A : lmodType R) n :=
  @representative_coefficient S F L r hr R A n.

Theorem comparison_eq_value_iso (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n d :
    component (@comparison S F L r hr R A n) d =
    iso_hom (@primes_inverted_ran_value_iso S F L p hS sat d hp R localR A n).
Proof.
apply module_hom_ext=> z.
apply (@module_iso_hom_injective R _ _ (@structured_collection_limit_iso S F L p hS sat d R
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n))).
apply module_limit_val_injective; apply functional_extensionality_dep=> P.
refine (Logic.eq_trans (@structured_collection_limit_component S F L p hS sat d R
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)
  (module_hom_fun (component (@comparison S F L r hr R A n) d) z) P) _).
refine (Logic.eq_trans (@comparison_collection_value S F L p hS sat R A n d P z) _).
refine (Logic.eq_trans (Logic.eq_sym
  (@primes_inverted_ran_value_component S F L p hS sat d hp R localR A n P z)) _).
symmetry; exact (@structured_collection_limit_component S F L p hS sat d R
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)
  (module_hom_fun (iso_hom (@primes_inverted_ran_value_iso S F L p hS sat d hp R localR A n)) z) P).
Qed.

Definition primes_inverted_ran_iso (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n :
    @isomorphism (functor_category (opposite (index_category F)) (module_category R))
      (sylow_coefficient A n) (@native_ran_coefficient S F R A n).
Proof.
apply (@nat_iso_of_components _ _ (sylow_coefficient A n) (@native_ran_coefficient S F R A n)
  (fun d => @primes_inverted_ran_value_iso S F L p hS sat d hp R localR A n)).
move=> d e u; rewrite -!comparison_eq_value_iso.
exact (naturality (@comparison S F L r hr R A n) u).
Defined.

Theorem primes_inverted_ran_iso_hom (hp : prime p)
    (R : comPzRingType) (localR : DPPrimeLocalUniversal.primes_inverted p R)
    (A : lmodType R) n d :
    component (iso_hom (primes_inverted_ran_iso hp localR A n)) d =
    component (@comparison S F L r hr R A n) d.
Proof. symmetry; exact: comparison_eq_value_iso. Qed.

Definition field_ran_iso (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n :=
  primes_inverted_ran_iso (pcharf_prime charp)
    (@DPFusionCentricAcyclicity.field_local p K charp) A n.

Definition prime_local_algebra_ran_iso (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n :=
  primes_inverted_ran_iso hp (DPPrimeLocalModules.scalar_map_implies_primes_inverted hp phi) A n.
End Comparison.
End DPNormalizerOrdinaryRanSylowIso.
