(** Genuine inverse orbit categories, including their actual centric full
    subcategories, for a faithful embedding and its image carrier. *)
From mathcomp Require Import all_boot all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryReindex FusionMaps
  FusionSystems FusionOrbit FusionCentralizerMaps.
From DiazParkV16b Require Import FiniteGroupFusion FiniteGroupFusionEmbedding
  FiniteGroupFusionEmbeddingImage FiniteGroupFusionEmbeddingOrbitRaw
  FiniteGroupFusionEmbeddingOrbitClasses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionOrbit DPFiniteGroupFusionEmbeddingOrbit DPFiniteGroupFusionEmbeddingOrbitClasses.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFiniteGroupFusionEmbeddingOrbitEquivalence.
Section Equivalence.
Variables N G : finGroupType.
Variable E : {morphism [set: N] >-> G}.
Hypothesis injE : 'injm E.
Local Notation T := [the finGroupType of [subg (DPFiniteGroupFusionEmbeddingImage.image_group E)]%type].
Local Notation F := (DPFiniteGroupFusionEmbedding.system E).
Local Notation H := (DPFiniteGroupFusion.system (DPFiniteGroupFusionEmbeddingImage.image_group E)).
Local Notation obj := (forward_subgroup E).
Local Notation back := (backward_subgroup injE).

Definition image_reindexed := reindexed_category (orbit_category H) obj.

Definition forward_reindexed : functor (orbit_category F) image_reindexed.
Proof.
refine (@Build_functor (orbit_category F) image_reindexed
  (fun P => P) (fun P Q f => forward_orbit injE f) _ _).
- exact: forward_orbit_identity.
- exact: forward_orbit_compose.
Defined.

Definition backward_reindexed : functor image_reindexed (orbit_category F).
Proof.
refine (@Build_functor image_reindexed (orbit_category F)
  (fun P => P) (fun P Q f => backward_orbit injE f) _ _).
- exact: backward_orbit_identity.
- exact: backward_orbit_compose.
Defined.

Definition reindexed_isomorphism : category_isomorphism (orbit_category F) image_reindexed.
Proof.
refine (@Build_category_isomorphism _ _ forward_reindexed backward_reindexed _ _).
- apply (@functor_ext_pointwise (orbit_category F) (orbit_category F)
    (functor_comp forward_reindexed backward_reindexed) (functor_id (orbit_category F))
    (fun P => Logic.eq_refl P)).
  move=> P Q f; rewrite hom_transport_loop; exact: forward_backward_orbit.
- apply (@functor_ext_pointwise image_reindexed image_reindexed
    (functor_comp backward_reindexed forward_reindexed) (functor_id image_reindexed)
    (fun P => Logic.eq_refl P)).
  move=> P Q f; rewrite hom_transport_loop; exact: backward_forward_orbit.
Defined.

Definition orbit_isomorphism : category_isomorphism (orbit_category F) (orbit_category H) :=
  category_iso_trans reindexed_isomorphism
    (@reindex_category_isomorphism (orbit_category H) {group N} obj back
      (backward_forward injE) (forward_backward injE)).

Definition orbit_functor := category_iso_forward orbit_isomorphism.

Lemma orbit_functor_object P : fobj orbit_functor P = obj P.
Proof. reflexivity. Qed.

Lemma orbit_functor_class (P Q : {group N}) (f : DPFusionSystem.arrow F P Q) :
  fmap orbit_functor (orbit_class f) = orbit_class (forward_arrow injE f).
Proof. exact: forward_orbit_class. Qed.

Definition centric_forward (P : centric_object F) : centric_object H.
Proof. apply (Sub (obj (val P))); rewrite (forward_centric injE); exact (valP P). Defined.

Definition centric_backward (Q : centric_object H) : centric_object F.
Proof.
apply (Sub (back (val Q))).
rewrite -(forward_centric injE) backward_forward; exact (valP Q).
Defined.

Lemma centric_forward_backward P : centric_backward (centric_forward P) = P.
Proof. apply val_inj; exact: forward_backward. Qed.

Lemma centric_backward_forward Q : centric_forward (centric_backward Q) = Q.
Proof. apply val_inj; exact: backward_forward. Qed.

Definition centric_reindexed := reindexed_category (centric_orbit_category H) centric_forward.

Definition centric_forward_reindexed : functor (centric_orbit_category F) centric_reindexed.
Proof.
refine (@Build_functor (centric_orbit_category F) centric_reindexed
  (fun P => P) (fun P Q f => forward_orbit injE f) _ _).
- move=> P; exact (@forward_orbit_identity N G E injE (val P)).
- move=> P Q U f g; exact (@forward_orbit_compose N G E injE (val P) (val Q) (val U) f g).
Defined.

Definition centric_backward_reindexed : functor centric_reindexed (centric_orbit_category F).
Proof.
refine (@Build_functor centric_reindexed (centric_orbit_category F)
  (fun P => P) (fun P Q f => backward_orbit injE f) _ _).
- move=> P; exact (@backward_orbit_identity N G E injE (val P)).
- move=> P Q U f g; exact (@backward_orbit_compose N G E injE (val P) (val Q) (val U) f g).
Defined.

Definition centric_reindexed_isomorphism :
  category_isomorphism (centric_orbit_category F) centric_reindexed.
Proof.
refine (@Build_category_isomorphism _ _ centric_forward_reindexed centric_backward_reindexed _ _).
- apply (@functor_ext_pointwise (centric_orbit_category F) (centric_orbit_category F)
    (functor_comp centric_forward_reindexed centric_backward_reindexed)
    (functor_id (centric_orbit_category F)) (fun P => Logic.eq_refl P)).
  move=> P Q f; rewrite hom_transport_loop; exact: forward_backward_orbit.
- apply (@functor_ext_pointwise centric_reindexed centric_reindexed
    (functor_comp centric_backward_reindexed centric_forward_reindexed)
    (functor_id centric_reindexed) (fun P => Logic.eq_refl P)).
  move=> P Q f; rewrite hom_transport_loop; exact: backward_forward_orbit.
Defined.

Definition centric_orbit_isomorphism :
  category_isomorphism (centric_orbit_category F) (centric_orbit_category H) :=
  category_iso_trans centric_reindexed_isomorphism
    (@reindex_category_isomorphism (centric_orbit_category H) (centric_object F)
      centric_forward centric_backward centric_backward_forward centric_forward_backward).

Definition centric_orbit_functor := category_iso_forward centric_orbit_isomorphism.

Lemma centric_orbit_functor_object P : fobj centric_orbit_functor P = centric_forward P.
Proof. reflexivity. Qed.

Lemma centric_orbit_functor_class (P Q : centric_object F)
    (f : DPFusionSystem.arrow F (val P) (val Q)) :
  fmap centric_orbit_functor (orbit_class f) = orbit_class (forward_arrow injE f).
Proof. exact: forward_orbit_class. Qed.

Lemma forward_subgroup_ambient (P : {group N}) :
  DPFusionSubgroup.ambient (obj P) = DPFiniteGroupFusionEmbeddingImage.ambient E P.
Proof.
apply val_inj; apply/setP=> y; apply/idP/idP.
- move/morphimP=> [z _ /morphimP[x _ hx ->] ->].
  exact (DPFiniteGroupFusionEmbeddingImage.ambient_mem E hx).
- move/morphimP=> [x _ hx ->].
  exact (DPFusionSubgroup.ambient_mem (forward_mem E hx)).
Qed.
End Equivalence.
End DPFiniteGroupFusionEmbeddingOrbitEquivalence.

Check DPFiniteGroupFusionEmbeddingOrbitEquivalence.centric_orbit_isomorphism.
Print Assumptions DPFiniteGroupFusionEmbeddingOrbitEquivalence.orbit_isomorphism.
Print Assumptions DPFiniteGroupFusionEmbeddingOrbitEquivalence.centric_orbit_isomorphism.
Print Assumptions DPFiniteGroupFusionEmbeddingOrbitEquivalence.centric_orbit_functor_class.
