From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology matrix_normedtype subtype_topology
  sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialSetYoneda
  TopologicalCategory TopologicalSimplexBasic TopologicalSimplexAffine
  TopologicalSimplexContinuity GeometricRealizationCarrier
  GeometricRealizationUniversal GeometricRealizationMaps.

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope quotient_scope.
Local Open Scope classical_set_scope.

Module DPGeometricRealizationStandardSimplex.
Import DPSimplexCategory DPTopological DPGeometricRealization
  DPGeometricRealizationUniversal DPGeometricRealizationMaps.
Section Standard.
Variable Real : realType.
Variable n : nat.
Let D := DPSimplicialSet.standard_simplex n.

Definition standard_evaluation_family :
    simplex_family Real D (DPTopologicalSimplex.simplex_space Real n) :=
  fun k f t => DPTopologicalSimplexAffine.pushforward f t.

Lemma standard_evaluation_compatible : family_compatible standard_evaluation_family.
Proof.
move=> k l a f t; symmetry; exact: DPTopologicalSimplexAffine.pushforward_composition.
Qed.

Lemma standard_evaluation_family_continuous k (f : DPSimplicialSet.simplex D k) :
  continuous (@standard_evaluation_family k f).
Proof. exact: DPTopologicalSimplexContinuity.pushforward_continuous. Qed.

Definition standard_evaluation : hom topological_category (realization_space Real D)
    (DPTopologicalSimplex.simplex_space Real n) :=
  @descent_map Real D _ standard_evaluation_family standard_evaluation_compatible
    standard_evaluation_family_continuous.

Lemma standard_evaluation_characteristic k (f : ordinal_map k n)
    (t : DPTopologicalSimplex.simplex Real k) :
  standard_evaluation (@characteristic Real D k f t) =
    DPTopologicalSimplexAffine.pushforward f t.
Proof.
exact: (@descent_characteristic Real D _ standard_evaluation_family
  standard_evaluation_compatible k f t).
Qed.

Definition standard_inclusion : hom topological_category
    (DPTopologicalSimplex.simplex_space Real n) (realization_space Real D) :=
  @characteristic_map Real D n (ordinal_map_identity n).

Lemma standard_evaluation_inclusion :
  compose standard_inclusion standard_evaluation =
    @identity topological_category (DPTopologicalSimplex.simplex_space Real n).
Proof.
apply: topological_hom_ext => t.
change (standard_evaluation (@characteristic Real D n (ordinal_map_identity n) t) = t).
rewrite standard_evaluation_characteristic.
exact: DPTopologicalSimplexAffine.pushforward_identity.
Qed.

Lemma standard_characteristic_normalization k (f : ordinal_map k n)
    (t : DPTopologicalSimplex.simplex Real k) :
  @characteristic Real D k f t =
    @characteristic Real D n (ordinal_map_identity n)
      (DPTopologicalSimplexAffine.pushforward f t).
Proof.
have h := @characteristic_ordinal Real D k n f (ordinal_map_identity n) t.
have he : DPSimplicialSet.simplex_map D f (ordinal_map_identity n) = f.
  by apply: ordinal_map_ext => i.
by rewrite he in h.
Qed.

Lemma standard_inclusion_evaluation :
  compose standard_evaluation standard_inclusion =
    @identity topological_category (realization_space Real D).
Proof.
apply: topological_hom_ext => z.
have [[[k f] t] <-] := realization_class_surjective z.
change (@characteristic Real D n (ordinal_map_identity n)
  (standard_evaluation (@characteristic Real D k f t)) = @characteristic Real D k f t).
rewrite standard_evaluation_characteristic; symmetry; exact: standard_characteristic_normalization.
Qed.

Definition realized_standard_simplex_homeomorphism :
    homeomorphism (realization_space Real D) (DPTopologicalSimplex.simplex_space Real n) :=
  @Build_isomorphism topological_category _ _ standard_evaluation standard_inclusion
    standard_inclusion_evaluation standard_evaluation_inclusion.

End Standard.

Lemma standard_evaluation_natural (Real : realType) n m (a : ordinal_map n m) :
  compose (realization_map Real (DPSimplicialSet.standard_simplex_map a))
    (standard_evaluation Real m) =
  compose (standard_evaluation Real n) (DPTopologicalSimplexContinuity.simplex_map Real a).
Proof.
apply: topological_hom_ext => z.
have [[[k f] t] <-] := realization_class_surjective z.
change (standard_evaluation Real m
  (realization_map Real (DPSimplicialSet.standard_simplex_map a)
    (@characteristic Real (DPSimplicialSet.standard_simplex n) k f t)) =
  DPTopologicalSimplexAffine.pushforward a (standard_evaluation Real n
    (@characteristic Real (DPSimplicialSet.standard_simplex n) k f t))).
rewrite realization_map_characteristic !standard_evaluation_characteristic.
symmetry; exact: DPTopologicalSimplexAffine.pushforward_composition.
Qed.

Lemma realization_characteristic_comparison (Real : realType)
    (X : DPSimplicialSet.simplicial_set) n (x : DPSimplicialSet.simplex X n) :
  compose (standard_inclusion Real n)
    (realization_map Real (DPSimplicialYoneda.characteristic_simplex X x)) =
    @characteristic_map Real X n x.
Proof.
apply: topological_hom_ext => t.
change (realization_map Real (DPSimplicialYoneda.characteristic_simplex X x)
  (@characteristic Real (DPSimplicialSet.standard_simplex n) n (ordinal_map_identity n) t) =
  @characteristic Real X n x t).
rewrite realization_map_characteristic.
change (@characteristic Real X n
  (DPSimplicialSet.simplex_map X (ordinal_map_identity n) x) t = @characteristic Real X n x t).
by rewrite DPSimplicialSet.simplex_map_identity.
Qed.

End DPGeometricRealizationStandardSimplex.
