From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology subtype_topology sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplexCategoryFactorization
  SimplexCategoryFactorizationSections SimplexCategoryFactorizationProperties
  SimplicialSet SimplicialSubcomplex SimplicialBoundary TopologicalCategory
  TopologicalSimplexBasic TopologicalSimplexAffine GeometricRealizationCarrier
  GeometricRealizationBoundaryAffine GeometricRealizationBoundaryFaces
  GeometricRealizationBoundarySupport GeometricRealizationBoundaryEvaluation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Module DPRealizationBoundaryNormalization.
Import DPSimplexCategory DPSimplexFactorization DPSimplexSections
  DPSimplexFactorizationProperties DPSimplicialSet DPSimplicialSubcomplex
  DPTopologicalSimplexAffine DPGeometricRealization
  DPRealizationBoundaryAffine DPRealizationBoundaryFaces DPRealizationBoundarySupport
  DPRealizationBoundaryEvaluation.

Section SupportFactor.
Variable Real : realType.
Variables k n : nat.
Variable f : ordinal_map k n.
Variable hf : ordinal_injective f.
Variable t : DPTopologicalSimplex.simplex Real k.
Let u := pushforward f t.

Lemma support_factor_hit i :
  f (vertex_preimage f (support_inclusion u i)) = support_inclusion u i.
Proof.
apply: vertex_preimage_hit.
case: (pselect (exists j, f j = support_inclusion u i)) => [h|h]; first exact h.
have hm := @face_inclusion_mem n (point_support u) (point_support_positive u) i.
change (is_true (support_inclusion u i \in point_support u)) in hm.
rewrite /point_support inE in hm.
have hz : DPTopologicalSimplex.coordinate u (support_inclusion u i) = 0.
  apply: pushforward_missing_coordinate => j hj; apply: h; by exists j.
by move: hm; rewrite hz eqxx.
Qed.

Lemma support_factor_monotone (i j : 'I_(face_dimension (point_support u)).+1) : (i <= j)%N ->
  (vertex_preimage f (support_inclusion u i) <= vertex_preimage f (support_inclusion u j))%N.
Proof.
move=> hij.
rewrite <- (@ordinal_injective_reflects_order k n f hf).
rewrite !support_factor_hit. exact (ordinal_monotone (support_inclusion u) hij).
Qed.

Definition support_factor : ordinal_map (face_dimension (point_support u)) k :=
  @OrdinalMap _ _ (fun i => vertex_preimage f (support_inclusion u i)) support_factor_monotone.

Lemma support_factorization : ordinal_map_compose support_factor f = support_inclusion u.
Proof. apply: ordinal_map_ext; exact: support_factor_hit. Qed.

Lemma support_factor_point : pushforward support_factor (support_point u) = t.
Proof.
apply: (@pushforward_injective Real k n f hf).
rewrite pushforward_composition.
have he : (f \o support_factor) = support_inclusion u.
  apply: funext => i; exact: support_factor_hit.
rewrite he support_point_evaluation. reflexivity.
Qed.

End SupportFactor.

Section Normalization.
Variable Real : realType.
Variable n : nat.
Let D := DPSimplicialBoundary.boundary_set n.

Lemma boundary_characteristic_injective_normalization k (f : ordinal_map k n)
    (hb : ~ ordinal_surjective f) (hf : ordinal_injective f)
    (t : DPTopologicalSimplex.simplex Real k) :
  @characteristic Real D k (exist _ f hb) t =
    boundary_normal_form (@boundary_evaluation_family Real n k (exist _ f hb) t).
Proof.
pose u := pushforward f t.
have h := @characteristic_ordinal Real D _ k (@support_factor Real k n f hf t)
  (exist _ f hb) (support_point u).
have he : simplex_map D (@support_factor Real k n f hf t) (exist _ f hb) =
    support_boundary_simplex (@boundary_evaluation_family Real n k (exist _ f hb) t).
  apply: subcomplex_simplex_ext. exact: support_factorization.
rewrite he support_factor_point in h. symmetry; exact h.
Qed.

Lemma boundary_image_nonsurjective k (f : ordinal_map k n)
    (hf : ~ ordinal_surjective f) : ~ ordinal_surjective (image_injection f).
Proof.
move=> hi; apply: hf; rewrite <- (image_factorization f).
exact: (ordinal_compose_surjective (@image_surjection_surjective k n f) hi).
Qed.

Lemma boundary_characteristic_normalization k (f : ordinal_map k n)
    (hf : ~ ordinal_surjective f) (t : DPTopologicalSimplex.simplex Real k) :
  @characteristic Real D k (exist _ f hf) t =
    boundary_normal_form (@boundary_evaluation_family Real n k (exist _ f hf) t).
Proof.
pose i := image_injection f.
pose q := image_surjection f.
pose hi := @boundary_image_nonsurjective k f hf.
have h := @characteristic_ordinal Real D k _ q (exist _ i hi) t.
have he : simplex_map D q (exist _ i hi) = exist _ f hf.
  apply: subcomplex_simplex_ext. exact: image_factorization.
rewrite he in h. transitivity (@characteristic Real D _ (exist _ i hi) (pushforward q t));
  first exact h.
rewrite (@boundary_characteristic_injective_normalization _ i hi
  (@image_injection_injective k n f) (pushforward q t)).
apply: f_equal. apply: val_inj.
change (pushforward i (pushforward q t) = pushforward f t).
rewrite pushforward_composition.
have heq : (i \o q) = f by apply: funext => j; exact: image_factorization_apply.
by rewrite heq.
Qed.

Theorem boundary_evaluation_normal_form z :
  boundary_normal_form (boundary_evaluation Real n z) = z.
Proof.
have [[[k [f hf]] t] <-] := realization_class_surjective z.
rewrite boundary_evaluation_characteristic.
symmetry; exact: boundary_characteristic_normalization.
Qed.

Theorem boundary_evaluation_injective : injective (boundary_evaluation Real n).
Proof.
move=> x y e.
rewrite <- (boundary_evaluation_normal_form x).
rewrite <- (boundary_evaluation_normal_form y). by rewrite e.
Qed.

End Normalization.
End DPRealizationBoundaryNormalization.
