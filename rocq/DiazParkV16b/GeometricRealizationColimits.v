(** Genuine colimit preservation by the constructed realization functor. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category CategoryLimits CategoryColimitMaps.
From DiazParkV16b Require Import SimplicialSet SimplicialSetYoneda
  TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps
  GeometricRealizationSingularAdjunction AdjunctionColimits.

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPGeometricRealizationColimits.
Import DPSimplicialYoneda DPTopological DPGeometricRealization
  DPGeometricRealizationMaps DPGeometricRealizationSingularAdjunction
  DPAdjunctionColimits.
Section Colimits.
Variable Real : realType.

Definition realization_colimit {I : category} {F : functor I simplicial_category}
    (K : colimiting_cocone F) :
    colimiting_cocone (functor_comp F (realization_functor Real)) :=
  left_adjoint_colimit (realization_singular_adjunction Real) K.

Lemma realization_colimit_object {I : category} {F : functor I simplicial_category}
    (K : colimiting_cocone F) :
  colimit_object (realization_colimit K) = realization_space Real (colimit_object K).
Proof. reflexivity. Qed.

Lemma realization_colimit_leg {I : category} {F : functor I simplicial_category}
    (K : colimiting_cocone F) (i : I) :
  cocone_leg (colimit_cocone (realization_colimit K)) i =
    realization_map Real (cocone_leg (colimit_cocone K) i).
Proof. reflexivity. Qed.

Lemma realization_colimit_map {I : category} {F G : functor I simplicial_category}
    (K : colimiting_cocone F) (J : colimiting_cocone G) (a : nat_trans F G) :
  realization_map Real (colimit_map K J a) =
    colimit_map (realization_colimit K) (realization_colimit J)
      (nat_whisker_right a (realization_functor Real)).
Proof.
exact (@left_adjoint_colimit_map simplicial_category topological_category
  (realization_functor Real) (singular_functor Real)
  (realization_singular_adjunction Real) I F G K J a).
Qed.

Definition realization_colimit_homeomorphism {I : category}
    {F : functor I simplicial_category} (K : colimiting_cocone F)
    (J : colimiting_cocone (functor_comp F (realization_functor Real))) :
    homeomorphism (realization_space Real (colimit_object K)) (colimit_object J) :=
  colimit_unique_iso (realization_colimit K) J.

Lemma realization_colimit_homeomorphism_leg {I : category}
    {F : functor I simplicial_category} (K : colimiting_cocone F)
    (J : colimiting_cocone (functor_comp F (realization_functor Real))) (i : I) :
  compose (realization_map Real (cocone_leg (colimit_cocone K) i))
    (iso_hom (realization_colimit_homeomorphism K J)) = cocone_leg (colimit_cocone J) i.
Proof.
change (compose (cocone_leg (colimit_cocone (realization_colimit K)) i)
  (colimit_map (realization_colimit K) J (nat_id _)) = cocone_leg (colimit_cocone J) i).
rewrite colimit_map_fac; exact: compose_id_left.
Qed.

End Colimits.
End DPGeometricRealizationColimits.
