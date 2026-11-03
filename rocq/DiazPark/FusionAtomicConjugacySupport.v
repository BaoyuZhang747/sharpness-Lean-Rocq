From mathcomp Require Import all_boot all_algebra all_fingroup.
From DiazPark Require Import Category CategoryFinite CategoryModules CategoryDerivedLimits
  CategoryAtomicDeletionFiltration CategoryAtomicDeletionTheorem FusionMaps FusionSystems
  FusionConjugacy FusionOrbit FusionOrbitRanks FusionFiniteCategory FusionCentricBasics
  FusionRadical FusionAtomicConjugacy BurnsideFusionRanks.
Import DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAtomicConjugacySupport.
Section Representative.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation C := (DPFusionFinite.centric_finite_category F).

Definition normalized_object (q : centric_object F) : centric_object F :=
  Sub (DPFusionConjugacy.normalized_representative F (val q))
    (DPFusionCentricBasics.centric_conjugate
      (DPFusionConjugacy.normalized_representative_spec F (val q)).1 (valP q)).
Lemma normalized_conjugate q :
  DPFusionSystem.conjugate F (val q) (val (normalized_object q)).
Proof. exact: (DPFusionConjugacy.normalized_representative_spec F (val q)).1. Qed.
Lemma normalized_fully_normalized q :
  DPFusionSystem.fully_normalized F (val (normalized_object q)).
Proof. exact: DPFusionConjugacy.normalized_representative_fully_normalized. Qed.

Definition conjugate_iso (q r : centric_object F)
    (h : DPFusionSystem.conjugate F (val q) (val r)) :
    @isomorphism (centric_orbit_category F) q r.
Proof.
have [f /andP[hf /eqP onto]] := sigW (existsP h).
pose a : DPFusionSystem.arrow F (val q) (val r) := Sub f hf.
exact (@DPBurnsideFusionRanks.centric_equal_rank_iso S F q r (orbit_class a)
  (DPFusionConjugacy.conjugate_card h)).
Defined.
Definition normalized_iso q := conjugate_iso (normalized_conjugate q).
Lemma normalized_nonradical p q :
  ~ DPFusionRadical.radical F p (val q) ->
  ~ DPFusionRadical.radical F p (val (normalized_object q)).
Proof.
by rewrite -(DPFusionAtomicConjugacy.radical_conjugate p (normalized_conjugate q)).
Qed.

Variable R : pzRingType.
Lemma atomic_support_transport (D : module_codiagram R (centric_orbit_category F))
    (q r : centric_object F) (e : @isomorphism (centric_orbit_category F) q r) :
  @coefficient_atomic C R D q -> @coefficient_atomic C R D r.
Proof.
move=> h x hxr; apply: h=> hxq; apply: hxr.
exact (@fc_isomorphic_trans C q x r hxq (@fc_related_of_iso C q r e)).
Qed.
Lemma normalized_atomic (D : module_codiagram R (centric_orbit_category F)) q :
  @coefficient_atomic C R D q -> @coefficient_atomic C R D (normalized_object q).
Proof. exact: atomic_support_transport (normalized_iso q). Qed.

(** This transport lemma discharges full normalization once the normalized
    vanishing theorem is supplied; it is not an additional fusion axiom. *)
Theorem atomic_vanishing_of_normalized p
    (normalized_vanishing : forall q : centric_object F,
      DPFusionSystem.fully_normalized F (val q) ->
      ~ DPFusionRadical.radical F p (val q) ->
      forall D : module_codiagram R (centric_orbit_category F),
        @coefficient_atomic C R D q -> derived_all_zero D)
    (q : centric_object F) (hn : ~ DPFusionRadical.radical F p (val q))
    (D : module_codiagram R (centric_orbit_category F))
    (hD : @coefficient_atomic C R D q) : derived_all_zero D.
Proof.
exact (normalized_vanishing (normalized_object q) (normalized_fully_normalized q)
  (normalized_nonradical hn) D (normalized_atomic hD)).
Qed.
End Representative.
End DPFusionAtomicConjugacySupport.


