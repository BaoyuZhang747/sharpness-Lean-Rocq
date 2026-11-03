(** Actual realization of a simplicial cocone, with literal continuous components. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplicialSet SimplicialSetYoneda SimplicialReplacementConstants
 TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialSet DPSimplicialYoneda DPSimplicialReplacementConstants DPTopological DPGeometricRealization DPGeometricRealizationMaps.
Module DPRealizationTopologicalCocone.
Section Cocone.
Variable Real:realType.
Variable C:category.
Variable F:functor C simplicial_category.
Variable X:simplicial_set.
Variable a:nat_trans F (@constant_diagram C simplicial_category X).
Definition realized_cocone : nat_trans (functor_comp F (realization_functor Real))
 (@constant_diagram C topological_category (realization_space Real X)).
Proof.
refine (@Build_nat_trans C topological_category (functor_comp F (realization_functor Real))
 (@constant_diagram C topological_category (realization_space Real X))
 (fun c=>realization_map Real (component a c)) _).
move=>c d f.
change (@compose topological_category _ _ _ (fmap (realization_functor Real) (fmap F f)) (fmap (realization_functor Real) (component a d))=
 @compose topological_category _ _ _ (fmap (realization_functor Real) (component a c)) (@identity topological_category (realization_space Real X))).
rewrite -fmap_compose compose_id_right.
have e : @compose simplicial_category _ _ _ (fmap F f) (component a d)=component a c.
  have h:=naturality a f; rewrite compose_id_right in h; exact h.
by rewrite e.
Defined.
Lemma realized_cocone_component c : component realized_cocone c=realization_map Real (component a c).
Proof. reflexivity. Qed.
End Cocone.
End DPRealizationTopologicalCocone.
