From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology matrix_normedtype subtype_topology
  sigT_topology quotient_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplexCategory SimplicialSet SimplicialSetYoneda
  TopologicalCategory TopologicalSimplexBasic TopologicalSimplexAffine
  GeometricRealizationCarrier GeometricRealizationUniversal.

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope quotient_scope.
Local Open Scope classical_set_scope.

Module DPGeometricRealizationMaps.
Import DPSimplexCategory DPSimplicialYoneda DPTopological DPGeometricRealization
  DPGeometricRealizationUniversal.
Section Maps.
Variable Real : realType.

Definition realization_map_family {X Y : DPSimplicialSet.simplicial_set}
    (a : DPSimplicialSet.simplicial_map X Y) :
    simplex_family Real X (realization_space Real Y) :=
  fun n x t => @characteristic Real Y n (component a n x) t.

Lemma realization_map_family_compatible {X Y : DPSimplicialSet.simplicial_set}
    (a : DPSimplicialSet.simplicial_map X Y) :
  family_compatible (realization_map_family a).
Proof.
move=> n m f x t; rewrite /realization_map_family DPSimplicialSet.simplicial_map_naturality.
exact: characteristic_ordinal.
Qed.

Lemma realization_map_family_continuous {X Y : DPSimplicialSet.simplicial_set}
    (a : DPSimplicialSet.simplicial_map X Y) n (x : DPSimplicialSet.simplex X n) :
  continuous (@realization_map_family X Y a n x).
Proof. exact: characteristic_continuous. Qed.

Definition realization_map {X Y : DPSimplicialSet.simplicial_set}
    (a : DPSimplicialSet.simplicial_map X Y) :
    hom topological_category (realization_space Real X) (realization_space Real Y) :=
  @descent_map Real X (realization_space Real Y) (realization_map_family a)
    (@realization_map_family_compatible X Y a) (@realization_map_family_continuous X Y a).

Lemma realization_map_characteristic {X Y : DPSimplicialSet.simplicial_set}
    (a : DPSimplicialSet.simplicial_map X Y) n (x : DPSimplicialSet.simplex X n) t :
  realization_map a (@characteristic Real X n x t) =
    @characteristic Real Y n (component a n x) t.
Proof.
exact: (@descent_characteristic Real X (realization_space Real Y)
  (realization_map_family a) (@realization_map_family_compatible X Y a) n x t).
Qed.

Lemma realization_map_identity (X : DPSimplicialSet.simplicial_set) :
  realization_map (nat_id X) = @identity topological_category (realization_space Real X).
Proof.
apply: topological_hom_ext => z.
have [[[n x] t] <-] := realization_class_surjective z.
change (realization_map (nat_id X) (@characteristic Real X n x t) =
  @characteristic Real X n x t).
by rewrite realization_map_characteristic.
Qed.

Lemma realization_map_composition {X Y Z : DPSimplicialSet.simplicial_set}
    (a : DPSimplicialSet.simplicial_map X Y) (b : DPSimplicialSet.simplicial_map Y Z) :
  realization_map (nat_comp a b) = compose (realization_map a) (realization_map b).
Proof.
apply: topological_hom_ext => z.
have [[[n x] t] <-] := realization_class_surjective z.
change (realization_map (nat_comp a b) (@characteristic Real X n x t) =
  realization_map b (realization_map a (@characteristic Real X n x t))).
by rewrite !realization_map_characteristic.
Qed.

Definition realization_functor : functor simplicial_category topological_category.
Proof.
refine (@Build_functor simplicial_category topological_category (realization_space Real)
  (fun X Y a => realization_map a) _ _).
- exact: realization_map_identity.
- move=> X Y Z a b; exact: realization_map_composition.
Defined.

End Maps.
End DPGeometricRealizationMaps.
