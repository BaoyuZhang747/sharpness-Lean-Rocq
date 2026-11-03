(** The actual centric-orbit collection application of finite atomic deletion.
    The current constructor takes nonradical atomic vanishing explicitly;
    the saturation theorem is supplied by the separate atomic comparison. *)
From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryModules CategoryDerivedLimits
  CategoryAtomicDeletionCore CategoryAtomicDeletionTheorem CategoryAtomicDeletionFiltration
  FusionMaps FusionSystems FusionOrbit FusionConjugacy FusionOrbitRanks FusionFiniteCategory
  FusionRadical BurnsideFusionRanks.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusion DPFusionSystem DPFusionOrbit DPFusionConjugacy
  DPFusionRanks DPFusionFinite DPBurnsideFusionRanks.
Local Open Scope group_scope.

Module DPFusionCollectionAcyclicity.
Section Collection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable H : {group S} -> Prop.
Hypothesis Hconj : forall P Q, DPFusionSystem.conjugate F P Q -> H P -> H Q.
Hypothesis Hover : forall (P Q : {group S}), P \subset Q -> H P -> H Q.

Definition centric_collection (P : centric_object F) : Prop := H (val P).
Definition collection_orbit_category :=
  @full_subcategory (centric_orbit_category F) centric_collection.

Lemma allowed_source_image_conjugate (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
  DPFusionSystem.conjugate F P (DPFusion.image (val f)).
Proof.
pose fi : DPFusionSystem.arrow F P (DPFusion.image (val f)) :=
  Sub (DPFusion.to_image (val f)) (DPFusionSystem.image_closed (valP f)).
apply: (DPFusionRanks.orbit_equal_rank_conjugate (DPFusionOrbit.orbit_class fi)).
symmetry; exact: DPFusionConjugacy.map_image_card.
Qed.

Lemma centric_collection_upward (P Q : centric_orbit_category F)
    (f : hom (centric_orbit_category F) P Q) : centric_collection P -> centric_collection Q.
Proof.
move=> hP; apply: (Hover (DPFusion.image_sub (val (repr f)))).
exact: Hconj (allowed_source_image_conjugate (repr f)) hP.
Qed.

Lemma centric_rank_equal_related P Q
    (f : fc_hom (centric_finite_category F) P Q) :
  centric_rank P = centric_rank Q -> @fc_isomorphic (centric_finite_category F) P Q.
Proof. move=> h; exact: fc_related_of_iso (centric_equal_rank_iso f h). Qed.

Variable R : pzRingType.
Definition collection_restriction := @full_restriction R (centric_orbit_category F) centric_collection.
Variable p : nat.
Hypothesis Hradical : forall P, DPFusionSystem.centric F P -> DPFusionRadical.radical F p P -> H P.

Hypothesis nonradical_atomic_vanishing : forall q : centric_object F,
  ~ DPFusionRadical.radical F p (val q) ->
  forall D : module_codiagram R (centric_orbit_category F),
    @coefficient_atomic (centric_finite_category F) R D q -> derived_all_zero D.

Theorem collection_acyclic_of_atomic_vanishing
    (D : module_codiagram R (centric_orbit_category F)) :
  derived_positive_zero D <-> derived_positive_zero (fobj collection_restriction D).
Proof.
apply: (@finite_collection_acyclic_iff (centric_finite_category F)
  (@centric_rank S F) (@centric_rank_le S F) (@centric_rank_equal_related)
  R centric_collection centric_collection_upward _ D).
move=> q hq E hE; apply: (@nonradical_atomic_vanishing q _ E hE).
move=> hr; apply hq; exact: Hradical (valP q) hr.
Qed.

Theorem collection_all_zero_of_atomic_vanishing
    (D : module_codiagram R (centric_orbit_category F)) :
  derived_all_zero D <-> derived_all_zero (fobj collection_restriction D).
Proof.
apply: (@finite_collection_all_zero_iff (centric_finite_category F)
  (@centric_rank S F) (@centric_rank_le S F) (@centric_rank_equal_related)
  R centric_collection centric_collection_upward _ D).
move=> q hq E hE; apply: (@nonradical_atomic_vanishing q _ E hE).
move=> hr; apply hq; exact: Hradical (valP q) hr.
Qed.

End Collection.
End DPFusionCollectionAcyclicity.
