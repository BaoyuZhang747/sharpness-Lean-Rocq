(** The actual nerve and realization diagram of the enlarged linking
    categories, with the literal forgetful augmentation. *)
From mathcomp Require Import all_boot all_algebra all_fingroup all_classical reals topology.
From DiazPark Require Import Category CategoryIsomorphism CategoryExtensionality
  FusionSystems FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem SimplexCategoryTypes SimplexCategory
  SimplicialSet SimplicialSetYoneda CategoryNerve SimplicialReplacementConstants
  TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps
  RealizationTopologicalCocone.
From DiazParkBLO Require Import BLODiagram.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplicialSet DPSimplicialYoneda DPCategoryNerve
  DPSimplicialReplacementConstants DPTopological DPGeometricRealization
  DPGeometricRealizationMaps DPRealizationTopologicalCocone DPBLODiagram
  DPFusionCentralizerCoverProjection.

Module DPBLODiagramNerve.
Section Diagram.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Local Notation I := (opposite (elementary_category F p)).

Definition nerve_diagram : functor I simplicial_category.
Proof.
refine (@Build_functor I simplicial_category
  (fun E => nerve (enlarged_category L (val E)))
  (fun E E' u => nerve_map (precompose L u)) _ _).
- move=> E; apply nat_trans_ext=> n; apply type_morphism_ext=> s.
  change (functor_comp s (precompose L (DPFusionSystem.arrow_identity F (val E))) = s).
  by rewrite precompose_identity functor_comp_id_right.
- move=> E E' E'' u v; apply nat_trans_ext=> n; apply type_morphism_ext=> s.
  change (functor_comp s (precompose L (DPFusionSystem.arrow_compose v u)) =
    functor_comp (functor_comp s (precompose L u)) (precompose L v)).
  by rewrite precompose_composition functor_comp_assoc.
Defined.

Definition nerve_forgetful (E : I) :
    simplicial_map (fobj nerve_diagram E) (nerve (DPCentricLinking.linking_category L)) :=
  nerve_map (forgetful L (val E)).

Lemma nerve_forgetful_natural E E' (u : hom I E E') n s :
    component (nerve_forgetful E') n (component (fmap nerve_diagram u) n s) =
    component (nerve_forgetful E) n s.
Proof.
change (functor_comp (functor_comp s (precompose L u)) (forgetful L (val E')) =
  functor_comp s (forgetful L (val E))).
by rewrite functor_comp_assoc forgetful_precompose.
Qed.

Definition nerve_cocone : nat_trans nerve_diagram
    (@constant_diagram I simplicial_category (nerve (DPCentricLinking.linking_category L))).
Proof.
refine (@Build_nat_trans I simplicial_category nerve_diagram
  (@constant_diagram I simplicial_category (nerve (DPCentricLinking.linking_category L)))
  nerve_forgetful _).
move=> E E' u; apply nat_trans_ext=> n; apply type_morphism_ext=> s.
exact: nerve_forgetful_natural.
Defined.

Variable Real : realType.

Definition space_diagram : functor I topological_category :=
  functor_comp nerve_diagram (realization_functor Real).

Definition space_forgetful := realized_cocone Real nerve_cocone.

Lemma space_diagram_object E : fobj space_diagram E =
    realization_space Real (nerve (enlarged_category L (val E))).
Proof. reflexivity. Qed.

Lemma space_diagram_arrow E E' (u : hom I E E') :
    fmap space_diagram u = realization_map Real (nerve_map (precompose L u)).
Proof. reflexivity. Qed.

Lemma space_forgetful_component E : component space_forgetful E =
    realization_map Real (nerve_map (forgetful L (val E))).
Proof. reflexivity. Qed.
End Diagram.
End DPBLODiagramNerve.
