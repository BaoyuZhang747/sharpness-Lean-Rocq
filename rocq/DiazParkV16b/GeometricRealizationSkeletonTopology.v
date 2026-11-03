(** Literal exhaustive weak topology of the realized skeletal filtration. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology
  quotient_topology sigT_topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import SimplicialSet SimplicialSubcomplex SimplicialSkeleton
  SimplicialSkeletonAttachmentCover SimplicialSkeletonAttachmentRealization
  CategoryPushoutColimit TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Import numFieldTopology.Exports.

Module DPRealizationSkeletonTopology.
Import DPSimplicialSet DPSimplicialSubcomplex DPSimplicialSkeleton
  DPGeometricRealization DPGeometricRealizationMaps.

Definition realized_skeletal_attachment_pushout (Real : realType) X n :=
  DPCategoryPushoutColimit.mapped_span_colimit_pushout
    (DPSimplicialAttachmentRealization.realized_skeletal_attachment_colimit Real X n).

Section SkeletonTopology.
Variable Real : realType.
Variable X : simplicial_set.

Lemma realization_open_characteristic (U : set (realization_space Real X)) :
  open U <-> forall n (x : simplex X n), open ((@characteristic Real X n x) @^-1` U).
Proof.
change (open ((@realization_class Real X) @^-1` U) <->
  forall n (x : simplex X n), open ((@characteristic Real X n x) @^-1` U)).
rewrite sigT_openP; split.
- move=> h n x; exact: (h (existT _ n x)).
- move=> h [n x]; exact: (h n x).
Qed.

Lemma realization_closed_characteristic (U : set (realization_space Real X)) :
  closed U <-> forall n (x : simplex X n), closed ((@characteristic Real X n x) @^-1` U).
Proof.
rewrite -openC realization_open_characteristic.
split=> h n x.
- rewrite -openC; exact: (h n x).
- have hn := h n x; rewrite -openC in hn; exact hn.
Qed.

End SkeletonTopology.
Section SkeletonTopology.
Variable Real : realType.
Variable X : simplicial_set.

Definition realized_skeleton_inclusion n := realization_map Real (skeleton_inclusion X n).

Lemma realized_skeleton_cover (z : realization_space Real X) :
  exists n, range (realized_skeleton_inclusion n) z.
Proof.
have [[[n x] t] <-] := realization_class_surjective z.
exists n; exists (@characteristic Real (skeleton_set X n) n
  (exist _ x (skeleton_exhaustive x)) t); first exact I.
exact: realization_map_characteristic.
Qed.

Lemma realized_skeleton_range_mono n m (h : (n <= m)%N) :
  range (realized_skeleton_inclusion n) `<=` range (realized_skeleton_inclusion m).
Proof.
move=> z [y _ <-].
exists (realization_map Real (skeleton_transition X h) y); first exact I.
have e := realization_map_composition Real (skeleton_transition X h) (skeleton_inclusion X m).
rewrite skeleton_transition_inclusion in e.
have ee := f_equal (fun f : hom DPTopological.topological_category
  (realization_space Real (skeleton_set X n)) (realization_space Real X) => f y) e.
exact: (esym ee).
Qed.

Lemma realized_skeleton_weak_closed (U : set (realization_space Real X)) :
  (forall n, closed (realized_skeleton_inclusion n @^-1` U)) -> closed U.
Proof.
move=> h; apply/realization_closed_characteristic => n x.
have hn := (proj1 (@realization_closed_characteristic Real (skeleton_set X n)
  (realized_skeleton_inclusion n @^-1` U)) (h n)) n
    (exist _ x (skeleton_exhaustive x)).
have e : (@characteristic Real (skeleton_set X n) n
    (exist _ x (skeleton_exhaustive x))) @^-1`
      (realized_skeleton_inclusion n @^-1` U) = (@characteristic Real X n x) @^-1` U.
  apply/predeqP => t; change (U (realized_skeleton_inclusion n
    (@characteristic Real (skeleton_set X n) n (exist _ x (skeleton_exhaustive x)) t)) <->
      U (@characteristic Real X n x t)).
  by rewrite /realized_skeleton_inclusion realization_map_characteristic.
by rewrite e in hn.
Qed.
End SkeletonTopology.
End DPRealizationSkeletonTopology.
