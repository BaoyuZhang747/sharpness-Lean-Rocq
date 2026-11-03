(** The actual restriction from a chain automorphism group to an acting
    centric subgroup is natural for every simultaneous extension. *)
From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryModules FusionSystems FusionOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects LinkingChainAutomorphisms
  NormalizerChainIndexCategory NormalizerOrbitPairCategory NormalizerOrbitPairProjection
  NormalizerChainExtensions LinkingChainRestrictionMaps LinkingChainActingHom
  LinkingChainExtensionActingLift LinkingChainExtensionActingSquare
  GroupCohomologyBase GroupCohomologyFunctor GroupCohomologyPullback
  GroupCohomologyOrbitCoefficient LinkingCommaNaturality
  NormalizerOrdinaryCoefficient NormalizerOrdinaryChainComparison
  NormalizerProjectionCommaStructured.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChainIndex DPNormalizerOrbitPair
  DPLinkingChainRestrictionMaps DPLinkingChainActingHom
  DPLinkingChainExtensionActingLift DPLinkingChainExtensionActingSquare
  DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPGroupCohomologyOrbitCoefficient DPLinkingCommaNaturality
  DPNormalizerOrdinaryCoefficient DPNormalizerOrdinaryChainComparison.

Module DPNormalizerOrdinaryPairRestriction.
Section Restriction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation I := (index_category F).
Local Notation E := (pair_category F).
Local Notation proj := (DPNormalizerOrbitPairProjection.projection F).
Local Notation M := (@representative_coefficient S F L r hr R A n).
Local Notation B := (@DPNormalizerProjectionCommaStructured.pair_coefficient S F R
  (centric_coefficient F A n)).

Definition restriction_component (X : E) :
    module_hom (fobj M (fobj proj X)) (fobj B X) :=
  module_hom_comp (iso_hom (@chain_comparison S F L r hr R A n (chain_of X)))
    (pull A (acting_hom L (acting_normalizes X)) n).

Lemma extension_group_square (X Y : E)
    (f : DPFusionSystem.arrow F (val (acting X)) (val (acting Y)))
    (a : DPNormalizerChainExtensions.extension (chain_of X) (chain_of Y) (val f)) :
    group_hom_comp (acting_hom L (acting_normalizes X))
      (restriction_morphism (extension_chain_map L a (valP (acting X)))) =
    group_hom_comp (arrow_group_hom f) (acting_hom L (acting_normalizes Y)).
Proof.
apply group_morphism_ext=> x.
exact (@extension_acting_square S F L _ _ _ _ (val f) a (valP (acting X))
  (acting_normalizes X) (acting_normalizes Y) x).
Qed.

Lemma restriction_natural (X Y : E) (u : hom E X Y) :
    module_hom_comp (@fmap _ _ M (fobj proj Y) (fobj proj X) (fmap proj u))
      (restriction_component X) =
    module_hom_comp (restriction_component Y) (@fmap _ _ B Y X u).
Proof.
have [f [hf [a]]] := hom_compatible u.
have hB : @fmap _ _ B Y X u = pull A (arrow_group_hom f) n.
  change (orbit_pull A n (val u) = pull A (arrow_group_hom f) n).
  rewrite -hf orbit_pull_class; reflexivity.
rewrite /restriction_component.
change (compose (fmap M (fmap proj u))
  (compose (iso_hom (@chain_comparison S F L r hr R A n (chain_of X)))
    (pull A (acting_hom L (acting_normalizes X)) n)) =
  compose (compose (iso_hom (@chain_comparison S F L r hr R A n (chain_of Y)))
    (pull A (acting_hom L (acting_normalizes Y)) n)) (@fmap _ _ B Y X u)).
rewrite -compose_assoc.
have hn := @chain_comparison_naturality S F L r hr R A n _ _
  (extension_chain_map L a (valP (acting X))) (fmap proj u).
change (compose (fmap M (fmap proj u))
  (iso_hom (@chain_comparison S F L r hr R A n (chain_of X))) =
  compose (iso_hom (@chain_comparison S F L r hr R A n (chain_of Y)))
    (pull A (restriction_morphism (extension_chain_map L a (valP (acting X)))) n)) in hn.
rewrite hn.
rewrite !compose_assoc hB.
congr (compose (iso_hom (@chain_comparison S F L r hr R A n (chain_of Y))) _).
change (module_hom_comp
  (pull A (restriction_morphism (extension_chain_map L a (valP (acting X)))) n)
  (pull A (acting_hom L (acting_normalizes X)) n) =
  module_hom_comp (pull A (acting_hom L (acting_normalizes Y)) n)
    (pull A (arrow_group_hom f) n)).
rewrite -!pull_composition extension_group_square; reflexivity.
Qed.

Definition pair_native_restriction : nat_trans (functor_comp (functor_op proj) M) B.
Proof.
refine (@Build_nat_trans (opposite E) (module_category R)
  (functor_comp (functor_op proj) M) B restriction_component _).
move=> X Y u; exact: restriction_natural.
Defined.

Lemma pair_native_restriction_component (X : E) :
    component pair_native_restriction X =
    module_hom_comp (iso_hom (@chain_comparison S F L r hr R A n (chain_of X)))
      (pull A (acting_hom L (acting_normalizes X)) n).
Proof. reflexivity. Qed.
End Restriction.
End DPNormalizerOrdinaryPairRestriction.
