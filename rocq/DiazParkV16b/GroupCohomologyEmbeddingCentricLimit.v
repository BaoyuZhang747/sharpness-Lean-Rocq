(** Faithful-image centric limits, normalized to literal restriction in the
    original subgroup carrier. The image is assumed Sylow and its index scalar
    invertible; the stated coefficient specializations construct that scalar. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  CategoryModuleLimitFunctor CategoryLimitMaps CategoryAdjunction CategoryIsomorphism
  CategoryIsomorphismAdjunction HomologicalModuleIso HomologicalDiagramLimits FusionOrbit.
From DiazParkV16b Require Import GroupCohomologyBase GroupCohomologyFunctor
  GroupCohomologyPullback GroupCohomologyOrbitCoefficient GroupCohomologyHomogeneousComparison
  GroupCohomologyEmbeddingDiagramBase GroupCohomologyEmbeddingOrbitCoefficient
  FiniteGroupFusion FiniteGroupFusionEmbedding FiniteGroupFusionEmbeddingImage
  FiniteGroupFusionEmbeddingOrbit GroupCohomologyCentricLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPGroupCohomology DPGroupCohomologyFunctor DPGroupCohomologyPullback
  DPFiniteGroupFusionEmbeddingImage DPFiniteGroupFusionEmbeddingOrbitEquivalence
  DPGroupCohomologyEmbeddingDiagramBase DPGroupCohomologyEmbeddingOrbitCoefficient
  DPGroupCohomologyCentricLimit DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPGroupCohomologyEmbeddingCentricLimit.
Section Limit.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Variable injE : 'injm E.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable n : nat.
Local Notation F := (DPFiniteGroupFusionEmbedding.system E).
Local Notation H := (DPFiniteGroupFusion.system (image_group E)).
Local Notation D := (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n).
Local Notation I := (DPGroupCohomologyOrbitCoefficient.centric_coefficient H A n).
Local Notation T := (functor_op (centric_orbit_functor injE)).
Local Notation J := (functor_comp T I).

Definition image_limit_restriction_iso : @isomorphism (module_category R)
    (module_limit_type I) (module_limit_type J) :=
  left_adjoint_limit_iso
    (adjunction_op (category_iso_adjunction (category_iso_symm
      (centric_orbit_isomorphism injE)))) I (module_limit I) (module_limit J).

Lemma image_limit_restriction_component (v : module_limit_type I)
    (P : DPFusionOrbit.centric_object F) :
  module_limit_val (module_hom_fun (iso_hom image_limit_restriction_iso) v) P =
    module_limit_val v (centric_forward injE P).
Proof.
have he := @left_adjoint_limit_iso_hom _ _ _ _ _
  (adjunction_op (category_iso_adjunction (category_iso_symm
    (centric_orbit_isomorphism injE)))) I (module_limit I) (module_limit J).
rewrite /image_limit_restriction_iso he.
have hf := @limit_restrict_map_fac _ _ _ T I (module_limit I) (module_limit J) P.
exact (congr1 (fun f => module_hom_fun f v) hf).
Qed.

Definition image_limit_coefficient_iso : @isomorphism (module_category R)
    (module_limit_type J) (module_limit_type D) :=
  functor_iso (module_limit_functor R (opposite (DPFusionOrbit.centric_orbit_category F)))
    (iso_symm (centric_coefficient_nat_iso injE A n)).

Lemma image_limit_coefficient_component (v : module_limit_type J)
    (P : DPFusionOrbit.centric_object F) :
  module_limit_val (module_hom_fun (iso_hom image_limit_coefficient_iso) v) P =
    module_hom_fun (pull A (subgroup_image_hom (image_equivalence E) (val P)) n)
      (module_limit_val v P).
Proof.
change (module_limit_val (limit_action (iso_inv (centric_coefficient_nat_iso injE A n)) v) P =
  module_hom_fun (pull A (subgroup_image_hom (image_equivalence E) (val P)) n)
    (module_limit_val v P)).
rewrite limit_action_coordinate centric_coefficient_nat_iso_inv; reflexivity.
Qed.

Variable p : nat.
Variable hP : p.-Sylow([set: G]) (image_group E).
Variable u : R.
Variable hu : u * (indexg [set: G] (image_group E))%:R = 1.

Definition embedding_centric_limit_iso : @isomorphism (module_category R)
    (value R G A n) (module_limit_type D) :=
  module_iso_comp (@finite_group_centric_limit_iso G (image_group E) R A n p hP u hu)
    (module_iso_comp image_limit_restriction_iso image_limit_coefficient_iso).

Definition embedding_subgroup_hom (P : {group N}) : {morphism [set: [subg P]] >-> G} :=
  group_hom_comp (DPGroupCohomologyHomogeneousComparison.subgroup_inclusion_hom P) E.

Lemma embedding_subgroup_hom_factor (P : DPFusionOrbit.centric_object F) :
  group_hom_comp (subgroup_image_hom (image_equivalence E) (val P))
    (centric_ambient_inclusion (centric_forward injE P)) = embedding_subgroup_hom (val P).
Proof. apply DPGroupCohomologyOrbitCoefficient.group_morphism_ext=> x; reflexivity. Qed.

Theorem embedding_centric_limit_iso_component (P : DPFusionOrbit.centric_object F) z :
  module_limit_val (module_hom_fun (iso_hom embedding_centric_limit_iso) z) P =
    module_hom_fun (pull A (embedding_subgroup_hom (val P)) n) z.
Proof.
change (module_limit_val (module_hom_fun (iso_hom image_limit_coefficient_iso)
  (module_hom_fun (iso_hom image_limit_restriction_iso)
    (module_hom_fun (iso_hom
      (@finite_group_centric_limit_iso G (image_group E) R A n p hP u hu)) z))) P =
    module_hom_fun (pull A (embedding_subgroup_hom (val P)) n) z).
rewrite image_limit_coefficient_component image_limit_restriction_component
  finite_group_centric_limit_iso_component.
have he := congr1 (fun f => module_hom_fun f z)
  (@pull_composition R A _ _ _ (subgroup_image_hom (image_equivalence E) (val P))
    (centric_ambient_inclusion (centric_forward injE P)) n).
rewrite embedding_subgroup_hom_factor in he; exact: esym he.
Qed.
End Limit.
End DPGroupCohomologyEmbeddingCentricLimit.
