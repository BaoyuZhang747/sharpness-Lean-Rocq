From mathcomp Require Import all_ssreflect all_fingroup pgroup generic_quotient boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryReindex CategoryFibration
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionCentralizerMaps FusionCentralizer
  FusionCentralizerAmbient FusionSubsystemOrbit FusionCentralizerCover FusionCentralizerCoverProjection
  FusionCentralizerCoverFiberObjects FusionCentralizerCoverFiberMaps.
Import DPFusion DPFusionOrbit DPFusionSubgroup DPFusionSubsystem DPFusionCentralizerCover
  DPFusionCentralizerCoverProjection DPFusionCentralizerCoverFiberObjects DPFusionCentralizerCoverFiberMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverFiberIso.
Section Isomorphism.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation CC := (opposite (centric_orbit_category CF)).
Local Notation hH := (@DPFusionCentralizerAmbient.lift_allowed S F E).
Local Notation fo := (@fiber_of_local S F p pS sat B).
Local Notation Fib := (fiber_category (functor_op (projection F p)) B).
Local Notation RC := (reindexed_category Fib fo).

Definition fiber_reindexed_functor : functor CC RC.
Proof.
refine (@Build_functor CC RC (fun P => P)
  (fun P Q f => @fiber_map_local S F p pS sat B P Q f) _ _).
- move=> P; apply: fiber_hom_ext; apply: val_inj.
  exact (@fmap_id _ _ (DPFusionSubsystem.orbit_functor hH) (val P)).
- move=> P Q R f g; apply: fiber_hom_ext; apply: val_inj.
  exact (@fmap_compose _ _ (DPFusionSubsystem.orbit_functor hH) (val R) (val Q) (val P) g f).
Defined.

Definition local_reindexed_functor : functor RC CC.
Proof.
refine (@Build_functor RC CC (fun P => P)
  (fun P Q f => @local_map_fiber S F p pS sat B P Q f) _ _).
- move=> P; apply: (@fiber_map_local_injective S F p pS sat B P P).
  rewrite fiber_map_local_surjective.
  exact: esym (fmap_id fiber_reindexed_functor P).
- move=> P Q R f g; apply: (@fiber_map_local_injective S F p pS sat B P R).
  rewrite fiber_map_local_surjective.
  have he := fmap_compose fiber_reindexed_functor
    (@local_map_fiber S F p pS sat B P Q f) (@local_map_fiber S F p pS sat B Q R g).
  cbn [fmap fiber_reindexed_functor] in he.
  have ef := @fiber_map_local_surjective S F p pS sat B P Q f.
  have eg := @fiber_map_local_surjective S F p pS sat B Q R g.
  exact (eq_trans (f_equal2 (@Category.compose RC P Q R) (esym ef) (esym eg)) (esym he)).
Defined.

Lemma fiber_local_functor_identity :
  functor_comp fiber_reindexed_functor local_reindexed_functor = functor_id CC.
Proof.
apply (@functor_extensionality CC CC (functor_comp fiber_reindexed_functor local_reindexed_functor) (functor_id CC) (Logic.eq_refl _)).
apply: functional_extensionality_dep=> P; apply: functional_extensionality_dep=> Q.
apply: functional_extensionality_dep=> f; exact: local_map_fiber_cancel.
Qed.
Lemma local_fiber_functor_identity :
  functor_comp local_reindexed_functor fiber_reindexed_functor = functor_id RC.
Proof.
apply (@functor_extensionality RC RC (functor_comp local_reindexed_functor fiber_reindexed_functor) (functor_id RC) (Logic.eq_refl _)).
apply: functional_extensionality_dep=> P; apply: functional_extensionality_dep=> Q.
apply: functional_extensionality_dep=> f; exact: fiber_map_local_surjective.
Qed.

Definition reindexed_fiber_isomorphism : category_isomorphism CC RC :=
  @Build_category_isomorphism CC RC fiber_reindexed_functor local_reindexed_functor
    fiber_local_functor_identity local_fiber_functor_identity.

Definition centralizer_fiber_isomorphism : category_isomorphism CC Fib :=
  category_iso_trans reindexed_fiber_isomorphism
    (@reindex_category_isomorphism Fib (centric_object CF) fo
      (@local_of_fiber S F p B) (@fiber_local_cancel S F p pS sat B)
      (@local_fiber_cancel S F p pS sat B)).

Definition cover_ambient_functor :
  functor (opposite (centralized_category F p)) (opposite (orbit_category F)) :=
  functor_op (functor_comp (centralized_inclusion F p)
    (functor_comp (forget F p) (centric_inclusion F))).

Definition centralizer_ambient_functor : functor CC (opposite (orbit_category F)) :=
  functor_op (functor_comp (centric_inclusion CF) (DPFusionSubsystem.orbit_functor hH)).

Theorem fiber_ambient_functor_eq :
  functor_comp (category_iso_forward centralizer_fiber_isomorphism)
    (functor_comp (fiber_inclusion (functor_op (projection F p)) B) cover_ambient_functor) =
  centralizer_ambient_functor.
Proof.
apply (@functor_extensionality CC (opposite (orbit_category F))
  (functor_comp (category_iso_forward centralizer_fiber_isomorphism)
    (functor_comp (fiber_inclusion (functor_op (projection F p)) B) cover_ambient_functor))
  centralizer_ambient_functor (Logic.eq_refl _)).
reflexivity.
Qed.

End Isomorphism.
End DPFusionCentralizerCoverFiberIso.




