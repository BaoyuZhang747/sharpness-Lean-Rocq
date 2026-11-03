(** Literal injections and naturality of the actual realization-copower homeomorphism. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology sigT_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialSet SimplicialCopower TopologicalCategory
  TopologicalCoproductHomotopy GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationCopower.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialSet DPSimplicialCopower DPTopological DPTopologicalCoproductHomotopy
  DPGeometricRealization DPGeometricRealizationMaps DPGeometricRealizationCopower.
Local Opaque realization_copower_homeomorphism.

Module DPGeometricRealizationCopowerNaturality.
Section Naturality.
Variable Real : realType.
Variable I : Type.

Definition realization_copower_inclusion (X : simplicial_set) i (z : realization_space Real X) :=
  @copower_inverseK Real I X
    (existT (fun _ : [the choiceType of {classic I}] => realization_space Real X) i z).

Definition copower_family_realization_map {X Y : simplicial_set} (a : simplicial_map X Y) :
  continuousType (copower_realization_family Real I X) (copower_realization_family Real I Y) :=
  @family_map [the choiceType of {classic I}] (fun _ => realization_space Real X)
    (fun _ => realization_space Real Y) (fun _ => realization_map Real a).

Lemma copower_component_at {X Y : simplicial_set} (a : simplicial_map X Y) n i (x : simplex X n) :
  component (@copower_map I X Y a) n (i,x) = (i,component a n x).
Proof. reflexivity. Qed.

Lemma copower_family_realization_map_at {X Y : simplicial_set} (a : simplicial_map X Y) i z :
  copower_family_realization_map a
    (existT (fun _ : [the choiceType of {classic I}] => realization_space Real X) i z) =
  existT (fun _ : [the choiceType of {classic I}] => realization_space Real Y) i (realization_map Real a z).
Proof. reflexivity. Qed.

Theorem realization_copower_natural_at {X Y : simplicial_set} (a : simplicial_map X Y)
    (z : realization_space Real (copower I X)) :
  copower_forward Real I Y
    (realization_map Real (@copower_map I X Y a) z) =
  copower_family_realization_map a (copower_forward Real I X z).
Proof.
have [[[n [i x]] t] <-] := realization_class_surjective z.
change (copower_forward Real I Y
  (realization_map Real (@copower_map I X Y a) (@characteristic Real (copower I X) n (i,x) t)) =
  copower_family_realization_map a (copower_forward Real I X
    (@characteristic Real (copower I X) n (i,x) t))).
rewrite realization_map_characteristic copower_component_at !copower_forward_characteristic.
by rewrite copower_family_realization_map_at realization_map_characteristic.
Qed.

Theorem realization_copower_natural {X Y : simplicial_set} (a : simplicial_map X Y) :
  continuous_compose (realization_map Real (@copower_map I X Y a))
    (copower_forward Real I Y) =
  continuous_compose (copower_forward Real I X) (copower_family_realization_map a).
Proof. apply: topological_hom_ext => z; exact: realization_copower_natural_at. Qed.

End Naturality.
End DPGeometricRealizationCopowerNaturality.
