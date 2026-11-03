From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient pgroup.
From DiazPark Require Import Category CategoryExtensionality CategoryReindex CategoryModules
  CategoryNaturalIso FusionMaps FusionSystems FusionOrbit FusionSaturation FusionOuterOrbit
  MackeyPair MackeyPairDiagrams FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientNormalization FusionQuotientAutomorphisms FusionQuotientOrbitMaps
  FusionQuotientOrbitFunctor FusionQuotientCollection FusionMackeyQuotientPair.
Import DPFusionOrbit DPFusionOuterOrbit DPFusionQuotientConstruction
  DPFusionQuotientNormalization DPFusionQuotientAutomorphisms DPFusionQuotientOrbitMaps
  DPFusionMackeyQuotientPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionMackeyQuotientCoefficients.

Lemma transported_fmap_cancel (C D : category) (G : functor C D)
    (x y x' y' : C) (ex : x' = x) (ey : y' = y) (f : hom C x y) :
  hom_transport (f_equal (fobj G) ex) (f_equal (fobj G) ey)
    (fmap G (hom_transport (Logic.eq_sym ex) (Logic.eq_sym ey) f)) = fmap G f.
Proof. destruct ex, ey; reflexivity. Qed.

Lemma transported_pull_cancel (R : comPzRingType) (C : category) (M : mackey_pair R C)
    (x y x' y' : C) (ex : x' = x) (ey : y' = y) (f : hom C y x) :
  @hom_transport (module_category R) _ _ _ _
    (f_equal (pair_value M) ex) (f_equal (pair_value M) ey)
    (module_hom_of_linear (pair_pull M
      (@hom_transport C y x y' x' (Logic.eq_sym ey) (Logic.eq_sym ex) f))) =
  module_hom_of_linear (pair_pull M f).
Proof. destruct ex, ey; reflexivity. Qed.

Definition functor_equality_iso (C D : category) (F G : functor C D) (h : F = G) :
  @isomorphism (functor_category C D) F G.
Proof. destruct h; exact (@iso_refl (functor_category C D) F). Defined.

Section Coefficients.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Hypothesis kernel_trivial : forall (P : {group coset_of Z}) a,
  a \in 'ker (automorphism_morphism cZ P) ->
  forall x : pair_value M (preimage P), pair_push M (aut_orbit F (preimage P) a) x = x.
Let qM := quotient_pair kernel_trivial.

Definition containing_inclusion :
  functor (DPFusionQuotientOrbitFunctor.containing_category F Z) (orbit_category F) :=
  reindex_inclusion (orbit_category F) (fun P : DPFusionQuotientOrbitFunctor.containing_object Z => val P).

Theorem containing_coefficient_equality :
  functor_comp (functor_op (DPFusionQuotientOrbitFunctor.quotient_functor cZ)) (pair_codiagram qM) =
  functor_comp (functor_op containing_inclusion) (pair_codiagram M).
Proof.
apply (@functor_ext_pointwise (opposite (DPFusionQuotientOrbitFunctor.containing_category F Z))
  (module_category R)
  (functor_comp (functor_op (DPFusionQuotientOrbitFunctor.quotient_functor cZ)) (pair_codiagram qM))
  (functor_comp (functor_op containing_inclusion) (pair_codiagram M))
  (fun P : DPFusionQuotientOrbitFunctor.containing_object Z => f_equal (pair_value M) (preimage_of_quotient cZ (valP P)))).
move=> P Q f.
change (@hom_transport (module_category R) _ _ _ _
  (f_equal (pair_value M) (preimage_of_quotient cZ (valP P)))
  (f_equal (pair_value M) (preimage_of_quotient cZ (valP Q)))
  (module_hom_of_linear (pair_pull qM (fmap (DPFusionQuotientOrbitFunctor.quotient_functor cZ) f))) =
  module_hom_of_linear (pair_pull M f)).
rewrite DPFusionQuotientOrbitFunctor.quotient_functor_map.
have h : module_hom_of_linear (pair_pull qM (orbit_map cZ
    (@hom_transport (orbit_category F) (val Q) (val P)
      (preimage (val Q / Z)%G) (preimage (val P / Z)%G)
      (esym (preimage_of_quotient cZ (valP Q)))
      (esym (preimage_of_quotient cZ (valP P))) f))) =
  module_hom_of_linear (pair_pull M
    (@hom_transport (orbit_category F) (val Q) (val P)
      (preimage (val Q / Z)%G) (preimage (val P / Z)%G)
      (esym (preimage_of_quotient cZ (valP Q)))
      (esym (preimage_of_quotient cZ (valP P))) f)).
  apply: module_hom_ext=> x; exact: quotient_pair_pull.
rewrite h.
exact: (@transported_pull_cancel R (orbit_category F) M (val P) (val Q) _ _
  (preimage_of_quotient cZ (valP P)) (preimage_of_quotient cZ (valP Q)) f).
Qed.

Definition containing_coefficient_iso := functor_equality_iso containing_coefficient_equality.

Definition collection_inclusion :
  functor (DPFusionQuotientCollection.collection_category cZ) (orbit_category F) :=
  reindex_inclusion (orbit_category F) (fun P : DPFusionQuotientCollection.collection_object cZ => val P).

Variable p : nat.
Hypothesis pZ : p.-group Z.
Hypothesis sat : DPFusionSaturation.saturated F p.

Theorem collection_coefficient_equality :
  functor_comp
    (functor_op (DPFusionQuotientCollection.collection_quotient_functor cZ pZ sat))
    (pair_codiagram (pair_restrict qM (centric_inclusion (system cZ)))) =
  functor_comp (functor_op collection_inclusion) (pair_codiagram M).
Proof.
apply (@functor_ext_pointwise (opposite (DPFusionQuotientCollection.collection_category cZ))
  (module_category R)
  (functor_comp (functor_op (DPFusionQuotientCollection.collection_quotient_functor cZ pZ sat))
    (pair_codiagram (pair_restrict qM (centric_inclusion (system cZ)))))
  (functor_comp (functor_op collection_inclusion) (pair_codiagram M))
  (fun P : DPFusionQuotientCollection.collection_object cZ =>
    f_equal (pair_value M) (preimage_of_quotient cZ (DPFusionQuotientCollection.collection_contains P)))).
move=> P Q f.
change (@hom_transport (module_category R) _ _ _ _
  (f_equal (pair_value M) (preimage_of_quotient cZ (DPFusionQuotientCollection.collection_contains P)))
  (f_equal (pair_value M) (preimage_of_quotient cZ (DPFusionQuotientCollection.collection_contains Q)))
  (module_hom_of_linear (pair_pull qM
    (fmap (DPFusionQuotientCollection.collection_quotient_functor cZ pZ sat) f))) =
  module_hom_of_linear (pair_pull M f)).
rewrite DPFusionQuotientCollection.collection_quotient_map.
have h : module_hom_of_linear (pair_pull qM (orbit_map cZ
    (@hom_transport (orbit_category F) (val Q) (val P)
      (preimage (val Q / Z)%G) (preimage (val P / Z)%G)
      (esym (preimage_of_quotient cZ (DPFusionQuotientCollection.collection_contains Q)))
      (esym (preimage_of_quotient cZ (DPFusionQuotientCollection.collection_contains P))) f))) =
  module_hom_of_linear (pair_pull M
    (@hom_transport (orbit_category F) (val Q) (val P)
      (preimage (val Q / Z)%G) (preimage (val P / Z)%G)
      (esym (preimage_of_quotient cZ (DPFusionQuotientCollection.collection_contains Q)))
      (esym (preimage_of_quotient cZ (DPFusionQuotientCollection.collection_contains P))) f)).
  apply: module_hom_ext=> x; exact: quotient_pair_pull.
rewrite h.
exact: (@transported_pull_cancel R (orbit_category F) M (val P) (val Q) _ _
  (preimage_of_quotient cZ (DPFusionQuotientCollection.collection_contains P))
  (preimage_of_quotient cZ (DPFusionQuotientCollection.collection_contains Q)) f).
Qed.

Definition collection_coefficient_iso := functor_equality_iso collection_coefficient_equality.
End Coefficients.
End DPFusionMackeyQuotientCoefficients.
