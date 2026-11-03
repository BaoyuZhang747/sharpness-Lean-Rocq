(** Coefficient-natural native higher-limit cofinality through the literal
    category-bar pullback, under actual comma augmentation exactness. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryModules
  CategoryDerivedLimits BarComplex BarNaturality BarDerivedComparison CategoryComplexIso
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient CategoryComma.
From DiazParkV16b Require Import CategoryBarPullback CategoryInducedBarCofinality
  CategoryInducedBarPullbackIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarComplex DiazParkBarNaturality DiazParkBarDerivedComparison
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkHomologicalModuleIso
  DPCategoryBarPullbackMaps.
Local Open Scope ring_scope.
Local Opaque module_quotient.

Section NaturalComparison.
Variable R : comPzRingType.
Variables C D : category.
Variable q : functor C D.
Hypothesis commas_exact : forall d, category_string_augmented_exact R (structured_category q d).

Definition comma_exact_bar_pullback_iso (M : module_codiagram R D) n :
    @isomorphism (module_category R) [the lmodType R of cohomology (bar_complex M) n]
      [the lmodType R of cohomology (bar_complex (pullback_diagram q M)) n] :=
  @induced_bar_pullback_cohomology_iso R C D q
    (@induced_bar_augmentation_surjective_of_comma R C D q commas_exact)
    (@induced_bar_augmentation_exact_of_comma R C D q commas_exact)
    (@induced_bar_successor_exact_of_comma R C D q commas_exact) M n.

Lemma comma_exact_bar_pullback_iso_hom (M : module_codiagram R D) n
    (z : cohomology (bar_complex M) n) :
    module_hom_fun (iso_hom (comma_exact_bar_pullback_iso M n)) z =
    cohomology_map (bar_pullback_cochain_map q M) n z.
Proof. exact: induced_bar_pullback_cohomology_iso_hom. Qed.

Definition comma_exact_bar_pullback_nat_iso n : @isomorphism
    (functor_category (functor_category (opposite D) (module_category R)) (module_category R))
    (@bar_cohomology_functor R D n)
    (functor_comp (precomposition (module_category R) (functor_op q))
      (@bar_cohomology_functor R C n)).
Proof.
refine (@nat_iso_of_components
  (functor_category (opposite D) (module_category R)) (module_category R)
  (@bar_cohomology_functor R D n)
  (functor_comp (precomposition (module_category R) (functor_op q))
    (@bar_cohomology_functor R C n)) (fun M => comma_exact_bar_pullback_iso M n) _).
intros M N u; apply module_hom_ext; intro z.
change (module_hom_fun (iso_hom (comma_exact_bar_pullback_iso N n))
  (cohomology_map (bar_cochain_map u) n z) =
  cohomology_map (bar_cochain_map (nat_whisker_left (functor_op q) u)) n
    (module_hom_fun (iso_hom (comma_exact_bar_pullback_iso M n)) z)).
rewrite !comma_exact_bar_pullback_iso_hom.
apply cohomology_map_square.
intros k a; exact: bar_pullback_coefficient_naturality.
Defined.

Definition comma_exact_higher_limit_iso (M : module_codiagram R D) n :
    @isomorphism (module_category R) (derived_limit R M n)
      (derived_limit R (pullback_diagram q M) n) :=
  module_iso_comp (iso_symm (bar_derived_limit_iso M n))
    (module_iso_comp (comma_exact_bar_pullback_iso M n)
      (bar_derived_limit_iso (pullback_diagram q M) n)).

Definition comma_exact_higher_limit_trans n : nat_trans
    (derived_limit_functor R (opposite D) n)
    (functor_comp (precomposition (module_category R) (functor_op q))
      (derived_limit_functor R (opposite C) n)) :=
  nat_comp (iso_inv (@bar_derived_limit_natural_iso R D n))
    (nat_comp (iso_hom (comma_exact_bar_pullback_nat_iso n))
      (nat_whisker_left (precomposition (module_category R) (functor_op q))
        (iso_hom (@bar_derived_limit_natural_iso R C n)))).

Definition comma_exact_higher_limit_nat_iso n : @isomorphism
    (functor_category (functor_category (opposite D) (module_category R)) (module_category R))
    (derived_limit_functor R (opposite D) n)
    (functor_comp (precomposition (module_category R) (functor_op q))
      (derived_limit_functor R (opposite C) n)).
Proof.
refine (@nat_iso_of_components
  (functor_category (opposite D) (module_category R)) (module_category R)
  (derived_limit_functor R (opposite D) n)
  (functor_comp (precomposition (module_category R) (functor_op q))
    (derived_limit_functor R (opposite C) n)) (fun M => comma_exact_higher_limit_iso M n) _).
intros M N u.
exact (naturality (comma_exact_higher_limit_trans n) u).
Defined.

Theorem comma_exact_higher_limit_iso_hom (M : module_codiagram R D) n
    (z : derived_limit R M n) :
    module_hom_fun (iso_hom (comma_exact_higher_limit_iso M n)) z =
    module_hom_fun (iso_hom (bar_derived_limit_iso (pullback_diagram q M) n))
      (cohomology_map (bar_pullback_cochain_map q M) n
        (module_hom_fun (iso_inv (bar_derived_limit_iso M n)) z)).
Proof.
change (module_hom_fun (iso_hom (bar_derived_limit_iso (pullback_diagram q M) n))
  (module_hom_fun (iso_hom (comma_exact_bar_pullback_iso M n))
    (module_hom_fun (iso_inv (bar_derived_limit_iso M n)) z)) =
  module_hom_fun (iso_hom (bar_derived_limit_iso (pullback_diagram q M) n))
    (cohomology_map (bar_pullback_cochain_map q M) n
      (module_hom_fun (iso_inv (bar_derived_limit_iso M n)) z))).
by rewrite comma_exact_bar_pullback_iso_hom.
Qed.
End NaturalComparison.

Arguments comma_exact_higher_limit_nat_iso R {C D} q commas_exact n.
Arguments comma_exact_higher_limit_iso R {C D} q commas_exact M n.
