(** The canonical directed-colimit comparison for actual right-derived
    limits over a finite category.  The bar comparison is a proved natural
    isomorphism with independently constructed injective-resolution limits. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryAdjointUniqueness CategoryFinite CategoryModules CategoryModuleLinear
  CategoryLimits CategoryColimitMaps CategoryDerivedLimits HomologicalComplex
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalCohomology HomologicalCohomologyMaps BarComplex BarNaturality
  BarDerivedComparison.
From DiazParkV29 Require Import FilteredLimitsDirected FilteredLimitsMaps
  FilteredLimitsCohomology FilteredLimitsDiagrams FilteredLimitsBar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFilteredLimits DPFilteredMaps DPFilteredCohomology
  DPFilteredDiagrams DPFilteredBar DiazParkHomological DiazParkCohomology
  DiazParkCohomologyMaps DiazParkBarComplex DiazParkBarNaturality
  DiazParkBarDerivedComparison.
Local Open Scope ring_scope.

Module DPFilteredDerived.
Section Comparison.
Variable R : pzRingType.
Variable I : directed_poset.
Variable C : finite_category.
Variable F : functor (stage_category I)
  (functor_category (opposite (fc_category C)) (module_category R)).

Definition derived_system (n : nat) : directed_module R I.
Proof.
refine (@DirectedModule R I (fun i => derived_limit R (fobj F i) n)
  (fun i j h => module_hom_to_linear (derived_limit_map R (fmap F h) n)) _ _).
- move=> i h x; replace h with (stage_refl i) by apply Prop_irrelevance.
  change (module_hom_fun (fmap (derived_limit_functor R (opposite (fc_category C)) n)
    (fmap F (@identity (stage_category I) i))) x = x).
  rewrite !fmap_id; reflexivity.
- move=> i j k h g x.
  exact (esym (congr1 (fun a : module_hom (derived_limit R (fobj F i) n)
    (derived_limit R (fobj F k) n) => module_hom_fun a x)
    (fmap_compose (functor_comp F (derived_limit_functor R (opposite (fc_category C)) n)) h g))).
Defined.

Definition comparison_forward n i :
    {linear dm_value (cohomology_system (bar_system F) n) i -> dm_value (derived_system n) i} :=
  module_hom_to_linear (iso_hom (bar_derived_limit_iso (fobj F i) n)).
Definition comparison_backward n i :
    {linear dm_value (derived_system n) i -> dm_value (cohomology_system (bar_system F) n) i} :=
  module_hom_to_linear (iso_inv (bar_derived_limit_iso (fobj F i) n)).

Lemma comparison_forward_natural n i j (h : stage_le i j) q :
    comparison_forward n j (dm_map (cohomology_system (bar_system F) n) h q) =
      dm_map (derived_system n) h (comparison_forward n i q).
Proof.
exact (congr1 (fun a : module_hom [the lmodType R of cohomology (bar_complex (fobj F i)) n]
    (derived_limit R (fobj F j) n) => module_hom_fun a q)
  (naturality (iso_hom (@bar_derived_limit_natural_iso R (fc_category C) n)) (fmap F h))).
Qed.
Lemma comparison_backward_natural n i j (h : stage_le i j) q :
    comparison_backward n j (dm_map (derived_system n) h q) =
      dm_map (cohomology_system (bar_system F) n) h (comparison_backward n i q).
Proof.
exact (congr1 (fun a : module_hom (derived_limit R (fobj F i) n)
    [the lmodType R of cohomology (bar_complex (fobj F j)) n] => module_hom_fun a q)
  (naturality (iso_inv (@bar_derived_limit_natural_iso R (fc_category C) n)) (fmap F h))).
Qed.

Definition colimit_forward n : module_hom
    (colimit_module (cohomology_system (bar_system F) n)) (colimit_module (derived_system n)) :=
  exist _ (direct_limit_map (comparison_forward n))
    (@direct_limit_map_linear R I _ _ (comparison_forward n) (@comparison_forward_natural n)).
Definition colimit_backward n : module_hom
    (colimit_module (derived_system n)) (colimit_module (cohomology_system (bar_system F) n)) :=
  exist _ (direct_limit_map (comparison_backward n))
    (@direct_limit_map_linear R I _ _ (comparison_backward n) (@comparison_backward_natural n)).

Lemma colimit_forward_in n i q :
    colimit_forward n (colimit_in (V := cohomology_system (bar_system F) n) (i := i) q) =
      colimit_in (V := derived_system n) (i := i) (comparison_forward n i q).
Proof.
exact (@direct_limit_map_in R I _ _ (comparison_forward n) (@comparison_forward_natural n) i q).
Qed.
Lemma colimit_backward_in n i q :
    colimit_backward n (colimit_in (V := derived_system n) (i := i) q) =
      colimit_in (V := cohomology_system (bar_system F) n) (i := i) (comparison_backward n i q).
Proof.
exact (@direct_limit_map_in R I _ _ (comparison_backward n) (@comparison_backward_natural n) i q).
Qed.

Definition colimit_bar_derived_iso n : @isomorphism (module_category R)
    (colimit_module (cohomology_system (bar_system F) n)) (colimit_module (derived_system n)).
Proof.
refine (@Build_isomorphism (module_category R) _ _ (colimit_forward n) (colimit_backward n) _ _).
- apply module_hom_ext=> q; have [i [x <-]] := colimit_in_surjective q.
  change (colimit_backward n (colimit_forward n (colimit_in x)) = colimit_in x).
  rewrite colimit_forward_in colimit_backward_in.
  congr (colimit_in _).
  exact (congr1 (fun f => module_hom_fun f x) (iso_hom_inv (bar_derived_limit_iso (fobj F i) n))).
- apply module_hom_ext=> q; have [i [x <-]] := colimit_in_surjective q.
  change (colimit_forward n (colimit_backward n (colimit_in x)) = colimit_in x).
  rewrite colimit_backward_in colimit_forward_in.
  congr (colimit_in _).
  exact (congr1 (fun f => module_hom_fun f x) (iso_inv_hom (bar_derived_limit_iso (fobj F i) n))).
Defined.

Definition higher_limit_colimit_iso n : @isomorphism (module_category R)
    (colimit_module (derived_system n)) (derived_limit R (pointwise_colimit F) n) :=
  isomorphism_composition (iso_symm (colimit_bar_derived_iso n))
    (isomorphism_composition (bar_colimit_iso F n) (bar_derived_limit_iso (pointwise_colimit F) n)).

Lemma higher_limit_colimit_iso_in n i (q : derived_limit R (fobj F i) n) :
    module_hom_fun (iso_hom (higher_limit_colimit_iso n))
      (colimit_in (V := derived_system n) (i := i) q) =
    module_hom_fun (derived_limit_map R (pointwise_leg F i) n) q.
Proof.
change (module_hom_fun (iso_hom (bar_derived_limit_iso (pointwise_colimit F) n))
    (module_hom_fun (iso_hom (bar_colimit_iso F n))
      (colimit_backward n (colimit_in (V := derived_system n) (i := i) q))) =
  module_hom_fun (derived_limit_map R (pointwise_leg F i) n) q).
rewrite colimit_backward_in bar_colimit_iso_in.
have h := congr1 (fun a : module_hom [the lmodType R of cohomology (bar_complex (fobj F i)) n]
    (derived_limit R (pointwise_colimit F) n) => module_hom_fun a (comparison_backward n i q))
  (naturality (iso_hom (@bar_derived_limit_natural_iso R (fc_category C) n)) (pointwise_leg F i)).
change (module_hom_fun (iso_hom (bar_derived_limit_iso (pointwise_colimit F) n))
  (cohomology_map (bar_leg F i) n (comparison_backward n i q)) =
  module_hom_fun (derived_limit_map R (pointwise_leg F i) n)
    (module_hom_fun (iso_hom (bar_derived_limit_iso (fobj F i) n)) (comparison_backward n i q))) in h.
rewrite h.
have he := congr1 (fun a => module_hom_fun a q) (iso_inv_hom (bar_derived_limit_iso (fobj F i) n)).
change (module_hom_fun (iso_hom (bar_derived_limit_iso (fobj F i) n)) (comparison_backward n i q) = q) in he.
rewrite he; reflexivity.
Qed.

End Comparison.
End DPFilteredDerived.
