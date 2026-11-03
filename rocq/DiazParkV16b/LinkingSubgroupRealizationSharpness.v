(** Actual singular subgroup coefficient vanishing, using the proved native coefficient identification and an explicit unit comparison. *)
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup zmodp all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness CategoryDerivedLimits FusionSystems FusionSaturation PrimeLocalUniversal.
From DiazParkV16b Require Import LinkingSystem SimplicialSet ChainQuasiIsomorphism RealizationUnitChains
 SingularCochainReplacementEdge LinkingSubgroupRealizationComparison GroupCohomologySharpness.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPSimplicialSet DPChainQuasiIsomorphism DPRealizationUnitChains DPSingularReplacementEdge DPLinkingSubgroupRealizationComparison.
Local Open Scope group_scope.
Local Open Scope ring_scope.
Module DPLinkingSubgroupRealizationSharpness.
Theorem field_positive_limits (Real:realType) (S:finGroupType) (F:DPFusionSystem.system S)
 (L:DPCentricLinking.system F) (p:nat) (hS:p.-group [set: S]) (sat:DPFusionSaturation.saturated F p)
 (K:fieldType) (charp:p \in [pchar K]) (A:lmodType K)
 (hunit:forall X:simplicial_set, quasi_isomorphism (realization_unit_chains Real [the comPzRingType of (K : Type)] X)) :
 singular_positive_limits_vanish Real A (subgroup_space_diagram Real L).
Proof.
move=>n j x.
pose e:=@subgroup_native_higher_limit_iso Real S F L [the comPzRingType of (K : Type)] hunit A n j.+1.
apply (module_iso_hom_injective (e:=e)); rewrite module_hom_zero.
exact: (@DPGroupCohomologySharpness.field_higher_limits_zero S F p hS sat K charp A n j).
Qed.
Theorem primes_inverted_positive_limits (Real:realType) (S:finGroupType) (F:DPFusionSystem.system S)
 (L:DPCentricLinking.system F) (p:nat) (hp:prime p) (hS:p.-group [set: S]) (sat:DPFusionSaturation.saturated F p)
 (R:comPzRingType) (localR:DPPrimeLocalUniversal.primes_inverted p R) (A:lmodType R)
 (hunit:forall X:simplicial_set, quasi_isomorphism (realization_unit_chains Real R X)) :
 singular_positive_limits_vanish Real A (subgroup_space_diagram Real L).
Proof.
move=>n j x.
pose e:=@subgroup_native_higher_limit_iso Real S F L R hunit A n j.+1.
apply (module_iso_hom_injective (e:=e)); rewrite module_hom_zero.
exact: (@DPGroupCohomologySharpness.primes_inverted_higher_limits_zero S F p hp hS sat R localR A n j).
Qed.
End DPLinkingSubgroupRealizationSharpness.
