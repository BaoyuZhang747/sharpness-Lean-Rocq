(** Actual realization-unit maps of simplicial replacements and their literal augmentation square. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality.
From DiazParkV16b Require Import SimplexCategoryTypes SimplexCategory SimplicialSet SimplicialSetYoneda CategoryNerve
 ChainComplex ChainQuasiIsomorphism ChainQuasiIsomorphismLaws SimplicialChains SimplicialChainsMaps
 BisimplicialSet BisimplicialChains BisimplicialAlexanderWhitneyNaturality
 SimplicialReplacementTypes SimplicialReplacement SimplicialReplacementMaps SimplicialReplacementConstants SimplicialReplacementAugmentation SimplicialReplacementComparisonPoly
 SingularSet TopologicalCategory GeometricRealizationCarrier GeometricRealizationMaps GeometricRealizationSingularAdjunction RealizationUnitChains.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPSimplicialTypes DPSimplexCategory DPSimplicialSet DPSimplicialYoneda DPCategoryNerve DPChainComplex DPChainQuasiIsomorphism DPChainQuasiIsomorphismLaws DPSimplicialChains DPSimplicialChainMaps
 DPBisimplicialSet DPBisimplicialChains DPAlexanderWhitneyNaturality DPSimplicialReplacementTypes DPSimplicialReplacement DPSimplicialReplacementMaps DPSimplicialReplacementConstants DPSimplicialReplacementAugmentation DPSimplicialReplacementComparisonPoly
 DPSingularSet DPTopological DPGeometricRealization DPGeometricRealizationMaps DPGeometricRealizationSingularAdjunction DPRealizationUnitChains.
Module DPRealizationReplacementUnit.
Section Diagram.
Variable Real:realType.
Variable C:category.
Variable F:functor C simplicial_category.
Local Notation H := (functor_comp (realization_functor Real) (singular_functor Real)).
Definition singular_realization_diagram : functor C simplicial_category := functor_comp F H.
Definition diagram_unit : nat_trans F singular_realization_diagram.
Proof.
refine (@Build_nat_trans C simplicial_category F singular_realization_diagram
 (fun c=>realization_unit_map Real (fobj F c)) _).
move=>c d f; exact: realization_unit_natural.
Defined.
Definition replacement_unit : simplicial_map (diagonal (replacement F))
 (diagonal (replacement singular_realization_diagram)) := diagonal_map (replacement_map diagram_unit).
Lemma replacement_unit_formula n (s:simplex (nerve C) n) (x:simplex (fobj F (initial_object s)) n) :
 component replacement_unit n (existT _ s x)=existT _ s
 (component (realization_unit_map Real (fobj F (initial_object s))) n x).
Proof. reflexivity. Qed.

Variable X:simplicial_set.
Variable a:nat_trans F (@constant_diagram C simplicial_category X).
Definition singular_realization_cocone : nat_trans singular_realization_diagram
 (@constant_diagram C simplicial_category (singular_set Real (realization_space Real X))).
Proof.
refine (@Build_nat_trans C simplicial_category singular_realization_diagram
 (@constant_diagram C simplicial_category (singular_set Real (realization_space Real X)))
 (fun c=>singular_map Real (realization_map Real (component a c))) _).
move=>c d f.
change (@compose simplicial_category _ _ _ (fmap H (fmap F f)) (fmap H (component a d))=
 @compose simplicial_category _ _ _ (fmap H (component a c)) (identity (fobj H X))).
rewrite -fmap_compose compose_id_right.
have e : @compose simplicial_category _ _ _ (fmap F f) (component a d)=component a c.
  have h:=naturality a f; rewrite compose_id_right in h; exact h.
by rewrite e.
Defined.

Definition singular_diagonal_augmentation := diagonal_coefficient_augmentation singular_realization_cocone.
Lemma replacement_unit_augmentation : nat_comp replacement_unit singular_diagonal_augmentation=
 nat_comp (diagonal_coefficient_augmentation a) (realization_unit_map Real X).
Proof.
apply nat_trans_ext=>n; apply type_morphism_ext=>[[s x]].
exact (Logic.eq_sym (f_equal (fun z:simplicial_map (fobj F (initial_object s)) (singular_set Real (realization_space Real X))=>component z n x)
 (realization_unit_natural Real (component a (initial_object s))))).
Qed.
End Diagram.

Section Comparison.
Variable Real:realType.
Variable R:pzRingType.
Variable C:category.
Variable F:functor C simplicial_category.
Variable hF:forall c, quasi_isomorphism (realization_unit_chains Real R (fobj F c)).
Theorem replacement_unit_quasi_isomorphism : quasi_isomorphism (chain_map_of R (replacement_unit Real F)).
Proof.
exact (@replacement_diagonal_quasi_isomorphism R C F (singular_realization_diagram Real F) (diagram_unit Real F) hF).
Qed.
Variable X:simplicial_set.
Variable a:nat_trans F (@constant_diagram C simplicial_category X).
Variable hX:quasi_isomorphism (realization_unit_chains Real R X).
Variable ha:quasi_isomorphism (chain_map_of R (diagonal_coefficient_augmentation a)).
Theorem singular_augmentation_quasi_isomorphism :
 quasi_isomorphism (chain_map_of R (singular_diagonal_augmentation Real a)).
Proof.
apply (@quasi_isomorphism_cancel_first R _ _ _ (chain_map_of R (replacement_unit Real F))
 (chain_map_of R (singular_diagonal_augmentation Real a))); first exact: replacement_unit_quasi_isomorphism.
apply (@quasi_isomorphism_ext R _ _
 (chain_composition (chain_map_of R (diagonal_coefficient_augmentation a)) (realization_unit_chains Real R X))
 (chain_composition (chain_map_of R (replacement_unit Real F)) (chain_map_of R (singular_diagonal_augmentation Real a)))).
- move=>n x; change (map_at R (realization_unit_map Real X) n (map_at R (diagonal_coefficient_augmentation a) n x)=
 map_at R (singular_diagonal_augmentation Real a) n (map_at R (replacement_unit Real F) n x)).
  by rewrite -!map_composition replacement_unit_augmentation.
- exact: quasi_isomorphism_composition ha hX.
Qed.
End Comparison.
End DPRealizationReplacementUnit.
