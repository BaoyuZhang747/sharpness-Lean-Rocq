(** Scalar restriction of actual right-derived limits, in every degree.
    The proof passes through the proved natural bar/injective comparison;
    no flatness, injective-preservation, or finite-generation premise. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryModuleExactness CategoryDerivedLimits
  CategoryEnoughInjectives CategoryInjectiveResolutionComparison
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  HomologicalScalarRestriction BarComplex BarNaturality BarDerivedComparison
  BarScalarComplex BarScalarNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DiazParkScalarRestriction DiazParkBarComplex
  DiazParkBarNaturality DiazParkBarDerivedComparison DiazParkBarScalarComplex
  DiazParkBarScalarNaturality.

Module DiazParkScalarHigherLimits.
Local Opaque chosen_injective_resolution injective_resolution_comparison.

Lemma bar_derived_naturality {R : pzRingType} {C : category}
    {D E : module_codiagram R C} (u : nat_trans D E) n
    (q : cohomology (bar_complex D) n) :
  module_hom_fun (derived_limit_map R u n)
    (module_hom_fun (iso_hom (bar_derived_limit_iso D n)) q) =
  module_hom_fun (iso_hom (bar_derived_limit_iso E n))
    (cohomology_map (bar_cochain_map u) n q).
Proof.
exact: (bar_injective_cohomology_naturality
  (injective_resolution_comparison (chosen_injective_resolution R D)
    (chosen_injective_resolution R E) u) q).
Qed.

Lemma bar_derived_inverse_naturality {R : pzRingType} {C : category}
    {D E : module_codiagram R C} (u : nat_trans D E) n (q : derived_limit R D n) :
  cohomology_map (bar_cochain_map u) n
    (module_hom_fun (iso_inv (bar_derived_limit_iso D n)) q) =
  module_hom_fun (iso_inv (bar_derived_limit_iso E n))
    (module_hom_fun (derived_limit_map R u n) q).
Proof.
apply (@module_iso_hom_injective R _ _ (bar_derived_limit_iso E n)).
rewrite -bar_derived_naturality !module_iso_inv_hom_apply; reflexivity.
Qed.

Section Scalars.
Variables A B : pzRingType.
Variable f : {rmorphism A -> B}.
Variable C : category.

Definition scalar_higher_limit_iso (D : module_codiagram B C) n :
    @isomorphism (module_category A) (restricted_module_type f (derived_limit B D n))
      (derived_limit A (restriction_diagram f D) n) :=
  module_iso_comp (functor_iso (restriction_functor f) (iso_symm (bar_derived_limit_iso D n)))
    (module_iso_comp (bar_scalar_cohomology_iso f D n)
      (bar_derived_limit_iso (restriction_diagram f D) n)).

Theorem scalar_higher_limit_naturality (D E : module_codiagram B C)
    (u : nat_trans D E) n (q : derived_limit B D n) :
  module_hom_fun (derived_limit_map A (restriction_map f u) n)
    (module_hom_fun (iso_hom (scalar_higher_limit_iso D n)) q) =
  module_hom_fun (iso_hom (scalar_higher_limit_iso E n))
    (module_hom_fun (restricted_hom f (derived_limit_map B u n)) q).
Proof.
change (module_hom_fun (derived_limit_map A (restriction_map f u) n)
  (module_hom_fun (iso_hom (bar_derived_limit_iso (restriction_diagram f D) n))
    (module_hom_fun (iso_hom (bar_scalar_cohomology_iso f D n))
      (module_hom_fun (iso_inv (bar_derived_limit_iso D n)) q))) =
  module_hom_fun (iso_hom (bar_derived_limit_iso (restriction_diagram f E) n))
    (module_hom_fun (iso_hom (bar_scalar_cohomology_iso f E n))
      (module_hom_fun (iso_inv (bar_derived_limit_iso E n))
        (module_hom_fun (derived_limit_map B u n) q)))).
rewrite bar_derived_naturality bar_scalar_cohomology_naturality.
congr (module_hom_fun _ (module_hom_fun _ _)).
exact: bar_derived_inverse_naturality.
Qed.

Definition scalar_higher_limit_natural_iso (n : nat) :
    @isomorphism (functor_category
      (functor_category (opposite C) (module_category B)) (module_category A))
    (functor_comp (derived_limit_functor B (opposite C) n) (restriction_functor f))
    (functor_comp (postcomposition (opposite C) (restriction_functor f))
      (derived_limit_functor A (opposite C) n)).
Proof.
apply: (@nat_iso_of_components _ _
  (functor_comp (derived_limit_functor B (opposite C) n) (restriction_functor f))
  (functor_comp (postcomposition (opposite C) (restriction_functor f))
    (derived_limit_functor A (opposite C) n))
  (fun D => scalar_higher_limit_iso D n)).
move=> D E u; apply module_hom_ext => q; symmetry.
exact: scalar_higher_limit_naturality.
Defined.

End Scalars.
End DiazParkScalarHigherLimits.
