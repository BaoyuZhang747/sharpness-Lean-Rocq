(** The actual radial relative comparison in arbitrary coordinates of a genuine pushout. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category.
From DiazParkV16b Require Import TopologicalCategory CategoryPushout TopologicalPushoutCarrier
  TopologicalPushoutUniversal TopologicalPushoutComparison TopologicalPushoutEmbedding TopologicalPushoutReparametrization
  SingularSimplexRadialFamily SingularSimplexRadialComplement SingularRadialAttachmentComparison
  SingularCohomology SingularChainMapsLaws SingularChainComparison SingularRelativePairs
  ChainComplex ChainMapImage ChainQuasiIsomorphism ChainQuasiIsomorphismLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPCategoryPushout DPTopologicalPushoutCarrier DPTopologicalPushoutUniversal
  DPTopologicalPushoutComparison DPTopologicalPushoutEmbedding DPTopologicalPushoutReparametrization
  DPSingularSimplexRadialFamily DPSingularSimplexRadialComplement DPSingularRadialAttachmentComparison
  DPSingularCohomology DPSingularChainMapsLaws DPSingularChainComparison DPSingularRelativePairs
  DPChainComplex DPChainMapImage DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws.
Module DPSingularRadialAttachmentCoordinates.
Section Coordinates.
Variable Real : realType.
Variable R : pzRingType.
Variable I : choiceType.
Variable d : I -> nat.
Variables A B X Y : topologicalType.
Variables (i : continuousType A B) (p : continuousType A X)
  (q : continuousType B Y) (j : continuousType X Y).
Variable h : @pushout_square topological_category A B X Y i p q j.
Variables (eA : homeomorphism A (boundary_family Real d)) (eB : homeomorphism B (cell_family Real d)).
Variable he : forall a, iso_hom eB (i a) = family_boundary_inclusion Real d (iso_hom eA a).
Let i0 := family_boundary_inclusion Real d.
Let p0 := continuous_compose (iso_inv eA) p.

Lemma coordinate_source_square a : iso_inv eB (i0 a) = i (iso_inv eA a).
Proof.
apply: (@homeomorphism_injective B (cell_family Real d) eB).
by rewrite homeomorphism_inverseK he homeomorphism_inverseK.
Qed.
Definition coordinate_pushout := @reparametrized_pushout A B X Y
  (boundary_family Real d) (cell_family Real d) i p q j h (iso_symm eA) (iso_symm eB) i0 coordinate_source_square.
Definition coordinate_target_homeomorphism := attaching_homeomorphism coordinate_pushout.

Lemma coordinate_original_square a : q (i a) = j (p a).
Proof. exact (congr1 (fun f : continuousType A Y => f a) (pushout_commutes h)). Qed.
Definition coordinate_attachment_relative := @singular_relative_map Real R A B X Y i j p q coordinate_original_square.
Definition coordinate_source_relative := @singular_relative_map Real R
  (boundary_family Real d) (cell_family Real d) A B i0 i
  (iso_inv eA) (iso_inv eB) coordinate_source_square.

Lemma coordinate_target_square x :
  iso_hom coordinate_target_homeomorphism (attaching_right_map i0 p0 x) = j (continuous_identity X x).
Proof. exact: attaching_homeomorphism_right. Qed.
Definition coordinate_target_relative := @singular_relative_map Real R
  X (attaching_space i0 p0) X Y (attaching_right_map i0 p0) j
  (continuous_identity X) (iso_hom coordinate_target_homeomorphism) coordinate_target_square.

Lemma coordinate_source_injective : injective i.
Proof.
move=> a b hab; apply: (@homeomorphism_injective A (boundary_family Real d) eA).
apply: (@boundary_family_inclusion_injective Real I d).
by rewrite -!he hab.
Qed.

Lemma coordinate_source_quasi_isomorphism : quasi_isomorphism coordinate_source_relative.
Proof.
apply: singular_relative_map_quasi_isomorphism.
- exact: boundary_family_inclusion_injective.
- exact: coordinate_source_injective.
- exact (@singular_homeomorphism_quasi_isomorphism Real R _ _ (iso_symm eA)).
- exact (@singular_homeomorphism_quasi_isomorphism Real R _ _ (iso_symm eB)).
Qed.
Lemma coordinate_target_quasi_isomorphism : quasi_isomorphism coordinate_target_relative.
Proof.
apply: singular_relative_map_quasi_isomorphism.
- exact (pushout_right_injective (attaching_pushout i0 p0) (@boundary_family_inclusion_injective Real I d)).
- exact (pushout_right_injective h coordinate_source_injective).
- apply: (@quasi_isomorphism_ext R _ _ (chain_identity _)).
  + move=> n x; symmetry; exact: singular_chain_identity.
  + exact: quasi_isomorphism_identity.
- exact (@singular_homeomorphism_quasi_isomorphism Real R _ _ coordinate_target_homeomorphism).
Qed.

Lemma coordinate_relative_square n x :
  chain_map_at coordinate_attachment_relative n (chain_map_at coordinate_source_relative n x) =
  chain_map_at coordinate_target_relative n (chain_map_at (@radial_attachment_relative_map Real R I d X p0) n x).
Proof.
have [b <-] := @relative_projection_surjective R _ _ (singular_chain_map Real R i0) n x.
rewrite /coordinate_source_relative
  (@singular_relative_map_projection Real R _ _ _ _ i0 i (iso_inv eA) (iso_inv eB) coordinate_source_square)
  /coordinate_attachment_relative
  (@singular_relative_map_projection Real R _ _ _ _ i j p q coordinate_original_square)
  /radial_attachment_relative_map
  (@singular_relative_map_projection Real R _ _ _ _ i0 (attaching_right_map i0 p0) p0
    (attaching_left_map i0 p0) (@radial_attachment_square Real I d X p0))
  /coordinate_target_relative
  (@singular_relative_map_projection Real R _ _ _ _ (attaching_right_map i0 p0) j
    (continuous_identity X) (iso_hom coordinate_target_homeomorphism) coordinate_target_square).
congr (chain_map_at (relative_projection (singular_chain_map Real R j)) n _).
rewrite -!singular_chain_composition.
have e : @compose topological_category _ _ _ (iso_inv eB) q =
    @compose topological_category _ _ _ (attaching_left_map i0 p0) (iso_hom coordinate_target_homeomorphism).
  apply: topological_hom_ext => z; symmetry; exact: attaching_homeomorphism_left.
by rewrite e.
Qed.

Theorem coordinate_attachment_relative_quasi_isomorphism : quasi_isomorphism coordinate_attachment_relative.
Proof.
apply: (@quasi_isomorphism_cancel_first R _ _ _ coordinate_source_relative coordinate_attachment_relative
  coordinate_source_quasi_isomorphism).
apply: (@quasi_isomorphism_ext R _ _
  (chain_composition (@radial_attachment_relative_map Real R I d X p0) coordinate_target_relative)).
- move=> n x; symmetry; exact: coordinate_relative_square.
- apply: quasi_isomorphism_composition; [exact: radial_attachment_relative_quasi_isomorphism |
    exact: coordinate_target_quasi_isomorphism].
Qed.
End Coordinates.
End DPSingularRadialAttachmentCoordinates.
