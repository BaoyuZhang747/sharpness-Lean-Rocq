(** The actual geometric-realization / singular-set adjunction.  The unit
    consists of characteristic simplices; the counit evaluates singular
    simplices and descends through the genuine all-ordinal quotient. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology matrix_normedtype subtype_topology
  sigT_topology quotient_topology.
From DiazPark Require Import Category CategoryExtensionality CategoryAdjunction.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet
  SimplicialSetYoneda TopologicalCategory TopologicalSimplexBasic
  TopologicalSimplexAffine TopologicalSimplexOrdinal SingularSet
  GeometricRealizationCarrier GeometricRealizationUniversal GeometricRealizationMaps.

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope quotient_scope.
Local Open Scope classical_set_scope.

Module DPGeometricRealizationSingularAdjunction.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda
  DPTopological DPSingularSet DPGeometricRealization
  DPGeometricRealizationUniversal DPGeometricRealizationMaps.
Section Adjunction.
Variable Real : realType.

Definition singular_functor : functor topological_category simplicial_category.
Proof.
refine (@Build_functor topological_category simplicial_category (singular_set Real)
  (fun X Y f => singular_map Real f) _ _).
- move=> X; apply: nat_trans_ext => n; apply: type_morphism_ext => s.
  exact: singular_map_identity.
- move=> X Y Z f g; apply: nat_trans_ext => n; apply: type_morphism_ext => s.
  exact: singular_map_composition.
Defined.

Definition realization_unit_map (X : simplicial_set) :
    simplicial_map X (singular_set Real (realization_space Real X)).
Proof.
refine (@Build_nat_trans (opposite simplex_category) type_category X
  (singular_set Real (realization_space Real X))
  (fun n x => @characteristic_map Real X n x) _).
move=> n m a; apply: type_morphism_ext => x.
apply: topological_hom_ext => t.
exact: characteristic_ordinal.
Defined.

Lemma realization_unit_at (X : simplicial_set) n (x : simplex X n) t :
  component (realization_unit_map X) n x t = @characteristic Real X n x t.
Proof. reflexivity. Qed.

Lemma realization_unit_natural {X Y : simplicial_set} (a : simplicial_map X Y) :
  nat_comp a (realization_unit_map Y) =
  nat_comp (realization_unit_map X) (singular_map Real (realization_map Real a)).
Proof.
apply: nat_trans_ext => n; apply: type_morphism_ext => x.
apply: topological_hom_ext => t.
change (@characteristic Real Y n (component a n x) t =
  realization_map Real a (@characteristic Real X n x t)).
symmetry; exact: realization_map_characteristic.
Qed.

Definition realization_unit : nat_trans (functor_id simplicial_category)
    (functor_comp (realization_functor Real) singular_functor).
Proof.
refine (@Build_nat_trans simplicial_category simplicial_category
  (functor_id simplicial_category)
  (functor_comp (realization_functor Real) singular_functor)
  realization_unit_map _).
move=> X Y a; exact: realization_unit_natural.
Defined.

Definition singular_evaluation_family (Y : topologicalType) :
    simplex_family Real (singular_set Real Y) Y := fun n s t => s t.

Lemma singular_evaluation_compatible (Y : topologicalType) :
  family_compatible (@singular_evaluation_family Y).
Proof. by move=> n m a s t. Qed.

Lemma singular_evaluation_family_continuous (Y : topologicalType) n
    (s : simplex (singular_set Real Y) n) :
  continuous (@singular_evaluation_family Y n s).
Proof. exact: cts_fun. Qed.

Definition realization_counit_map (Y : topologicalType) :
    hom topological_category (realization_space Real (singular_set Real Y)) Y :=
  @descent_map Real (singular_set Real Y) Y (@singular_evaluation_family Y)
    (@singular_evaluation_compatible Y) (@singular_evaluation_family_continuous Y).

Lemma realization_counit_characteristic (Y : topologicalType) n
    (s : simplex (singular_set Real Y) n) t :
  realization_counit_map Y (@characteristic Real (singular_set Real Y) n s t) = s t.
Proof.
exact: (@descent_characteristic Real (singular_set Real Y) Y
  (@singular_evaluation_family Y) (@singular_evaluation_compatible Y) n s t).
Qed.

Lemma realization_counit_natural {Y Z : topologicalType}
    (f : hom topological_category Y Z) :
  compose (realization_map Real (singular_map Real f)) (realization_counit_map Z) =
  compose (realization_counit_map Y) f.
Proof.
apply: topological_hom_ext => z.
have [[[n s] t] <-] := realization_class_surjective z.
change (realization_counit_map Z
  (realization_map Real (singular_map Real f)
    (@characteristic Real (singular_set Real Y) n s t)) =
  f (realization_counit_map Y (@characteristic Real (singular_set Real Y) n s t))).
by rewrite realization_map_characteristic !realization_counit_characteristic.
Qed.

Definition realization_counit : nat_trans
    (functor_comp singular_functor (realization_functor Real))
    (functor_id topological_category).
Proof.
refine (@Build_nat_trans topological_category topological_category
  (functor_comp singular_functor (realization_functor Real))
  (functor_id topological_category)
  realization_counit_map _).
move=> Y Z f; exact: realization_counit_natural.
Defined.

Lemma realization_triangle_left (X : simplicial_set) :
  compose (realization_map Real (realization_unit_map X))
    (realization_counit_map (realization_space Real X)) =
  @identity topological_category (realization_space Real X).
Proof.
apply: topological_hom_ext => z.
have [[[n x] t] <-] := realization_class_surjective z.
change (realization_counit_map (realization_space Real X)
  (realization_map Real (realization_unit_map X) (@characteristic Real X n x t)) =
  @characteristic Real X n x t).
by rewrite realization_map_characteristic realization_counit_characteristic.
Qed.

Lemma realization_triangle_right (Y : topologicalType) :
  nat_comp (realization_unit_map (singular_set Real Y))
    (singular_map Real (realization_counit_map Y)) = nat_id (singular_set Real Y).
Proof.
apply: nat_trans_ext => n; apply: type_morphism_ext => s.
apply: topological_hom_ext => t.
change (realization_counit_map Y (@characteristic Real (singular_set Real Y) n s t) = s t).
exact: realization_counit_characteristic.
Qed.

Definition realization_singular_adjunction :
    adjunction (realization_functor Real) singular_functor.
Proof.
refine (@Build_adjunction simplicial_category topological_category
  (realization_functor Real) singular_functor realization_unit realization_counit _ _).
- exact: realization_triangle_left.
- exact: realization_triangle_right.
Defined.

End Adjunction.
End DPGeometricRealizationSingularAdjunction.
