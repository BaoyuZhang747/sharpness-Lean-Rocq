(** Finite skeletal separation derived from the actual attaching pushouts.
    Boundary-family geometry is supplied and later discharged literally. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplicialSet SimplicialSubcomplex
  SimplicialSkeleton SimplicialSkeletonAttachmentStages SimplicialSkeletonAttachmentCover
  GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationSkeletonTopology
  GeometricRealizationSkeletonPushout
  TopologicalCategory TopologicalPushoutEmbedding TopologicalPushoutEmbeddingOpaque.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Module DPRealizationSkeletonFinite.
Import DPSimplicialTypes DPSimplicialSet DPSimplicialSubcomplex DPSimplicialSkeleton
  DPSimplicialAttachmentStages DPSimplicialAttachmentCover DPGeometricRealization
  DPGeometricRealizationMaps DPRealizationSkeletonTopology DPRealizationSkeletonPushout
  DPTopologicalPushoutEmbedding DPTopologicalPushoutEmbeddingOpaque.

Lemma empty_space_accessible (Y : topologicalType) (h : Y -> False) : accessible_space Y.
Proof. by move=> y; exfalso; exact: h y. Qed.

Lemma surjection_from_empty (E T : Type) (q : E -> T) (he : E -> False)
  (hq : forall t, exists e, q e = t) (t : T) : False.
Proof.
have [e _] := hq t; exact (he e).
Qed.

Definition realization_empty (Real : realType) (Y : simplicial_set)
  (h : forall n, simplex Y n -> False) :=
  @surjection_from_empty (pre_realization Real Y) (realization Real Y)
    (@realization_class Real Y)
    (fun p => @h (projT1 (projT1 p)) (projT2 (projT1 p)))
    (@realization_class_surjective Real Y).

Section Finite.
Variable Real : realType.
Variable X : simplicial_set.

Lemma stage_zero_simplex_empty n (x : simplex (stage_set X 0) n) : False.
Proof.
destruct x as [x hx].
have [m [y [f [hm he]]]] := hx.
by move: hm; rewrite ltn0.
Qed.

Definition realized_stage_zero_empty :=
  @realization_empty Real (stage_set X 0) stage_zero_simplex_empty.

Definition realized_stage_zero_accessible :=
  @empty_space_accessible (realization_space Real (stage_set X 0)) realized_stage_zero_empty.


Variable hboundary_injective : forall n, injective (realization_map Real (attaching_inclusion X n)).
Variable hboundary_closed : forall n (S : set (realization_space Real (boundary_copower X n))),
  @closed (realization_space Real (boundary_copower X n)) S ->
  @closed (realization_space Real (cell_copower X n))
    (realization_map Real (attaching_inclusion X n) @` S).
Variable hcells_T1 : forall n, accessible_space (realization_space Real (cell_copower X n)).

Definition realized_stage_step_injective n :=
  @actual_pushout_right_injective
    (realization_space Real (boundary_copower X n))
    (realization_space Real (cell_copower X n))
    (realization_space Real (stage_set X n))
    (realization_space Real (stage_set X n.+1))
    (realization_map Real (attaching_inclusion X n))
    (realization_map Real (attaching_map X n))
    (realization_map Real (attaching_cells X n))
    (realization_map Real (attaching_stage X n))
    (actual_skeletal_attachment_pushout Real X n) (@hboundary_injective n).

Lemma realized_stage_step_closed n
  (S : set (realization_space Real (stage_set X n))) (hS : closed S) :
  @closed (realization_space Real (stage_set X n.+1))
    (realization_map Real (attaching_stage X n) @` S).
Proof.
  refine (@actual_pushout_right_closed
    (realization_space Real (boundary_copower X n))
    (realization_space Real (cell_copower X n))
    (realization_space Real (stage_set X n))
    (realization_space Real (stage_set X n.+1))
    (realization_map Real (attaching_inclusion X n))
    (realization_map Real (attaching_map X n))
    (realization_map Real (attaching_cells X n))
    (realization_map Real (attaching_stage X n))
    (actual_skeletal_attachment_pushout Real X n)
    (@hboundary_injective n) _ S hS).
  intros T hT.
  apply (@hboundary_closed n).
  exact hT.
Qed.

Lemma realized_stage_accessible n : accessible_space (realization_space Real (stage_set X n)).
Proof.
elim: n => [|n ih]; first exact realized_stage_zero_accessible.
refine (@actual_pushout_accessible
  (realization_space Real (boundary_copower X n))
  (realization_space Real (cell_copower X n))
  (realization_space Real (stage_set X n))
  (realization_space Real (stage_set X n.+1))
  (realization_map Real (attaching_inclusion X n))
  (realization_map Real (attaching_map X n))
  (realization_map Real (attaching_cells X n))
  (realization_map Real (attaching_stage X n))
  (actual_skeletal_attachment_pushout Real X n) (@hboundary_injective n) _ _ ih).
- intros T hT; apply (@hboundary_closed n); exact hT.
- apply hcells_T1.
Qed.

Lemma skeleton_step_attaching n :
  skeleton_transition X (leqnSn n) = attaching_stage X n.+1.
Proof.
apply nat_trans_ext; intro k; apply type_morphism_ext; intro x.
apply subcomplex_simplex_ext; reflexivity.
Qed.

Lemma realized_skeleton_transition_identity n (h : (n <= n)%N) :
  realization_map Real (skeleton_transition X h) =
  @identity DPTopological.topological_category (realization_space Real (skeleton_set X n)).
Proof.
rewrite /skeleton_transition subcomplex_map_identity; exact: realization_map_identity.
Qed.

Lemma realized_skeleton_transition_composition n m k
  (hnm : (n <= m)%N) (hmk : (m <= k)%N) (hnk : (n <= k)%N) z :
  realization_map Real (skeleton_transition X hnk) z =
  realization_map Real (skeleton_transition X hmk)
    (realization_map Real (skeleton_transition X hnm) z).
Proof.
have e := realization_map_composition Real (skeleton_transition X hnm) (skeleton_transition X hmk).
rewrite (skeleton_transition_compose X hnm hmk hnk) in e.
exact: (f_equal (fun f : hom DPTopological.topological_category
  (realization_space Real (skeleton_set X n)) (realization_space Real (skeleton_set X k)) => f z) e).
Qed.

Theorem realized_skeleton_transition_injective n m (h : (n <= m)%N) :
  injective (realization_map Real (skeleton_transition X h)).
Proof.
elim: m => [|m ih] in n h *.
- have en : n = 0%N by apply/eqP; rewrite -leqn0; exact h.
  subst n.
  rewrite realized_skeleton_transition_identity; by move=> x y.
- have hor := h; rewrite leq_eqVlt in hor.
  move/orP: hor => [/eqP en|hlt].
  + subst n; rewrite realized_skeleton_transition_identity; by move=> x y.
  + have hnm : (n <= m)%N by rewrite -ltnS.
    move=> z w e; apply (ih n hnm).
    have hstep : injective (realization_map Real (skeleton_transition X (leqnSn m))).
      rewrite skeleton_step_attaching; exact: realized_stage_step_injective.
    apply hstep.
    rewrite -(realized_skeleton_transition_composition hnm (leqnSn m) h z)
      -(realized_skeleton_transition_composition hnm (leqnSn m) h w).
    exact e.
Qed.

Theorem realized_skeleton_transition_closed n m (h : (n <= m)%N)
  (S : set (realization_space Real (skeleton_set X n))) (hS : closed S) :
  closed (realization_map Real (skeleton_transition X h) @` S).
Proof.
elim: m => [|m ih] in n h S hS *.
- have en : n = 0%N by apply/eqP; rewrite -leqn0; exact h.
  subst n.
  rewrite realized_skeleton_transition_identity; change (closed (id @` S)).
  by rewrite image_id.
- have hor := h; rewrite leq_eqVlt in hor.
  move/orP: hor => [/eqP en|hlt].
  + subst n; rewrite realized_skeleton_transition_identity; change (closed (id @` S)).
    by rewrite image_id.
  + have hnm : (n <= m)%N by rewrite -ltnS.
    have ef : (fun z : realization_space Real (skeleton_set X n) =>
      realization_map Real (skeleton_transition X h) z) =
      (realization_map Real (skeleton_transition X (leqnSn m))) \o
      (realization_map Real (skeleton_transition X hnm)).
      apply: funext => z; exact: realized_skeleton_transition_composition.
    change (closed ((fun z : realization_space Real (skeleton_set X n) =>
      realization_map Real (skeleton_transition X h) z) @` S)).
    rewrite ef -image_comp skeleton_step_attaching.
    apply: realized_stage_step_closed; exact: (ih n hnm S hS).
Qed.
End Finite.
End DPRealizationSkeletonFinite.
