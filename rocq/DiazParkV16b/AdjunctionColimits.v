(** Left adjoints preserve actual colimits.  The mapped cocone and its
    universal descent are constructed, using the adjunction Hom maps. *)
From DiazPark Require Import Category CategoryLimits CategoryColimitMaps
  CategoryAdjunction CategoryInjectives.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module DPAdjunctionColimits.

Definition functor_cocone {I C D : category} (F : functor I C)
    (L : functor C D) {v : C} (s : cocone F v) :
    cocone (functor_comp F L) (fobj L v).
Proof.
  refine (@Build_cocone I D (functor_comp F L) (fobj L v)
    (fun i => fmap L (cocone_leg s i)) _).
  intros i j f. change (compose (fmap L (fmap F f))
    (fmap L (cocone_leg s j)) = fmap L (cocone_leg s i)).
  rewrite <- fmap_compose, cocone_natural. reflexivity.
Defined.

Section Adjunction.
Context {C D : category} {L : functor C D} {R : functor D C}.
Variable adj : adjunction L R.

Definition adjunction_cocone {I : category} (F : functor I C)
    {v : D} (s : cocone (functor_comp F L) v) : cocone F (fobj R v).
Proof.
  refine (@Build_cocone I C F (fobj R v)
    (fun i => adjoint_to_right adj (cocone_leg s i)) _).
  intros i j f. rewrite <- adjoint_to_right_precompose.
  change (adjoint_to_right adj (compose (fmap (functor_comp F L) f) (cocone_leg s j)) =
    adjoint_to_right adj (cocone_leg s i)).
  rewrite (cocone_natural s f). reflexivity.
Defined.

Definition left_adjoint_colimit {I : category} (F : functor I C)
    (K : colimiting_cocone F) : colimiting_cocone (functor_comp F L).
Proof.
  refine (@Build_colimiting_cocone I D (functor_comp F L)
    (fobj L (colimit_object K)) (functor_cocone L (colimit_cocone K))
    (fun v s => adjoint_to_left adj (colimit_desc K (adjunction_cocone (F:=F) s))) _ _).
  - intros v s i.
    change (compose (fmap L (cocone_leg (colimit_cocone K) i))
      (adjoint_to_left adj (colimit_desc K (adjunction_cocone (F:=F) s))) = cocone_leg s i).
    rewrite <- adjoint_to_left_precompose, colimit_desc_fac.
    apply adjoint_left_right.
  - intros v s f h.
    transitivity (adjoint_to_left adj (adjoint_to_right adj f)).
    + symmetry. apply adjoint_left_right.
    + apply f_equal. apply colimit_desc_unique. intro i.
      rewrite <- adjoint_to_right_precompose.
      change (adjoint_to_right adj (compose (fmap L (cocone_leg (colimit_cocone K) i)) f) =
        adjoint_to_right adj (cocone_leg s i)).
      apply f_equal. exact (h i).
Defined.

Lemma left_adjoint_colimit_object {I : category} (F : functor I C)
    (K : colimiting_cocone F) :
  colimit_object (left_adjoint_colimit K) = fobj L (colimit_object K).
Proof. reflexivity. Qed.

Lemma left_adjoint_colimit_leg {I : category} (F : functor I C)
    (K : colimiting_cocone F) (i : I) :
  cocone_leg (colimit_cocone (left_adjoint_colimit K)) i =
    fmap L (cocone_leg (colimit_cocone K) i).
Proof. reflexivity. Qed.

Lemma left_adjoint_colimit_map {I : category} {F G : functor I C}
    (K : colimiting_cocone F) (J : colimiting_cocone G) (a : nat_trans F G) :
  fmap L (colimit_map K J a) =
    colimit_map (left_adjoint_colimit K) (left_adjoint_colimit J)
      (nat_whisker_right a L).
Proof.
  apply (colimit_hom_ext (left_adjoint_colimit K)). intro i.
  transitivity (compose (fmap L (component a i))
    (fmap L (cocone_leg (colimit_cocone J) i))).
  - change (compose (fmap L (cocone_leg (colimit_cocone K) i)) (fmap L (colimit_map K J a)) =
      compose (fmap L (component a i)) (fmap L (cocone_leg (colimit_cocone J) i))).
    rewrite <- !fmap_compose, colimit_map_fac. reflexivity.
  - symmetry. exact (colimit_map_fac (left_adjoint_colimit K)
      (left_adjoint_colimit J) (nat_whisker_right a L) i).
Qed.

Definition left_adjoint_colimit_iso {I : category} {F : functor I C}
    (K : colimiting_cocone F) (J : colimiting_cocone (functor_comp F L)) :
    isomorphism (fobj L (colimit_object K)) (colimit_object J) :=
  colimit_unique_iso (left_adjoint_colimit K) J.

End Adjunction.
End DPAdjunctionColimits.
