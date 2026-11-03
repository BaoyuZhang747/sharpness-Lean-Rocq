(** The actual two ordinary-cohomology coefficients on the literal local
    normalizer collection agree through native subgroup restriction charts. *)
From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryNaturalIso FusionSystems FusionOrbit FusionSaturation FusionSubsystemOrbit.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainNormalizer
  ChainNormalizerFusionModel ChainNormalizerFusionOrbit
  GroupCohomologyPullback GroupCohomologyOrbitCoefficient
  GroupCohomologyEmbeddingDiagramBase GroupCohomologySubsystemCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPLinkingChains DPNormalizerChain DPChainNormalizerFusionModel
  DPChainNormalizerFusionOrbit DPGroupCohomologyPullback
  DPGroupCohomologyEmbeddingDiagramBase.
Local Open Scope group_scope.

Module DPChainNormalizerCohomologyCoefficient.
Section Coefficients.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable c : chain F.
Variable p : nat.
Variable sat : DPFusionSaturation.saturated F p.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation N := [the finGroupType of [subg (normalizer c)]%type].
Local Notation H := (local_system L c).
Local Notation X := (collection_category L c).
Local Notation incl := [morphism of @sgval S (normalizer c)].

Definition local_coefficient : module_codiagram R X :=
  functor_comp (functor_op (@collection_local_functor S F L c p sat))
    (DPGroupCohomologyOrbitCoefficient.centric_coefficient H A n).

Definition ambient_coefficient : module_codiagram R X :=
  functor_comp (functor_op (@collection_ambient_functor S F L c p sat))
    (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n).

Definition collection_object_iso (P : X) : @isomorphism (module_category R)
    (fobj local_coefficient P) (fobj ambient_coefficient P) :=
  subgroup_image_cohomology_iso (injm_sgval (normalizer c)) A n (val P).

Definition collection_coefficient_nat_iso :
    @isomorphism (functor_category (opposite X) (module_category R))
      local_coefficient ambient_coefficient.
Proof.
apply (@nat_iso_of_components _ _ local_coefficient ambient_coefficient collection_object_iso).
move=> Q P a; move: a; apply: quotW => a.
change (module_hom_comp
  (DPGroupCohomologyOrbitCoefficient.orbit_pull A n (DPFusionOrbit.orbit_class a))
  (iso_hom (collection_object_iso P)) =
  module_hom_comp (iso_hom (collection_object_iso Q))
    (DPGroupCohomologyOrbitCoefficient.orbit_pull A n
      (DPFusionSubsystem.orbit_map (@local_ambient_allowed S F L c p sat)
        (DPFusionOrbit.orbit_class a)))).
rewrite DPFusionSubsystem.orbit_map_class !DPGroupCohomologyOrbitCoefficient.orbit_pull_class.
exact (@DPGroupCohomologySubsystemCoefficient.raw_naturality S F (normalizer c) H
  (@local_ambient_allowed S F L c p sat) R A n (val P) (val Q) a).
Defined.

Theorem collection_coefficient_nat_iso_hom (P : X) :
  component (iso_hom collection_coefficient_nat_iso) P =
    pull A (subgroup_image_inverse (injm_sgval (normalizer c)) (val P)) n.
Proof. reflexivity. Qed.

Theorem collection_coefficient_nat_iso_inv (P : X) :
  component (iso_inv collection_coefficient_nat_iso) P =
    pull A (subgroup_image_hom incl (val P)) n.
Proof. reflexivity. Qed.

End Coefficients.
End DPChainNormalizerCohomologyCoefficient.
