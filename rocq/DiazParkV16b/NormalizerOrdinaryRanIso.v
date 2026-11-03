(** For any chain representatives, the explicitly constructed ordinary
    normalizer coefficient is the genuine right Kan coefficient. Its forward
    transformation is exactly the transpose of native subgroup restriction. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryNaturalIso HomologicalModuleIso
  FusionSystems FusionOrbit FusionSaturation PrimeLocalRing PrimeLocalUniversal
  PrimeLocalModules FusionCentricAcyclicity.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainIndexCategory
  NormalizerOrdinaryCoefficient NormalizerOrdinaryRepresentativeChange NormalizerOrdinaryRanMap
  NormalizerOrdinaryRanRepresentativeChange NormalizerOrdinaryRanSylowIso
  NormalizerProjectionCommaRepresentatives NormalizerProjectionCommaGroupLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPLinkingChains DPNormalizerChainIndex
  DPNormalizerOrdinaryCoefficient DPNormalizerOrdinaryRepresentativeChange
  DPNormalizerOrdinaryRanMap DPNormalizerOrdinaryRanRepresentativeChange
  DPNormalizerProjectionCommaRepresentatives DPNormalizerProjectionCommaGroupLimit
  DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerOrdinaryRanIso.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Local Notation s := (@index_representative S F L p hS sat).
Local Notation hs := (@index_representative_class S F L p hS sat).

Section LocalRing.
Variable hp : prime p.
Variable R : comPzRingType.
Variable localR : DPPrimeLocalUniversal.primes_inverted p R.
Variable A : lmodType R.
Variable n : nat.
Local Notation M := (@representative_coefficient S F L r hr R A n).
Local Notation K := (@native_ran_coefficient S F R A n).
Local Notation theta := (@representative_coefficient_iso S F L R A n r s hr hs).

Definition component_iso d : @isomorphism (module_category R) (fobj M d) (fobj K d) :=
  module_iso_comp (nat_iso_component theta d)
    (@primes_inverted_ran_value_iso S F L p hS sat d hp R localR A n).

Lemma component_iso_hom d : iso_hom (component_iso d) =
    component (@comparison S F L r hr R A n) d.
Proof.
change (module_hom_comp (component (iso_hom theta) d)
  (iso_hom (@primes_inverted_ran_value_iso S F L p hS sat d hp R localR A n)) =
  component (@comparison S F L r hr R A n) d).
rewrite -DPNormalizerOrdinaryRanSylowIso.comparison_eq_value_iso.
exact: comparison_representative_change.
Qed.

Definition primes_inverted_ran_iso :
    @isomorphism (functor_category (opposite (index_category F)) (module_category R)) M K.
Proof.
apply (@nat_iso_of_components _ _ M K component_iso).
move=> d e u; rewrite !component_iso_hom; exact (naturality (@comparison S F L r hr R A n) u).
Defined.

Theorem primes_inverted_ran_iso_hom d :
    component (iso_hom primes_inverted_ran_iso) d = component (@comparison S F L r hr R A n) d.
Proof. exact: component_iso_hom. Qed.
End LocalRing.

Definition field_ran_iso (K : fieldType) (charp : p \in [pchar K])
    (A : lmodType K) n :=
  primes_inverted_ran_iso (pcharf_prime charp) (@DPFusionCentricAcyclicity.field_local p K charp) A n.

Definition prime_local_algebra_ran_iso (hp : prime p)
    (R : comPzRingType) (phi : {rmorphism DPPrimeLocal.type p -> R})
    (A : lmodType R) n :=
  primes_inverted_ran_iso hp (DPPrimeLocalModules.scalar_map_implies_primes_inverted hp phi) A n.
End Comparison.
End DPNormalizerOrdinaryRanIso.
