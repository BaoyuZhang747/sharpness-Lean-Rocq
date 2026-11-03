(** The independently defined Ext from the constant regular module agrees
    naturally, in every degree, with native injective-resolution higher limits. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryDiagramHom CategoryDiagramHomComplex CategoryDiagramHomLimit
  CategoryDiagramExt CategoryComplexIso CategoryModuleLimits
  CategoryEnoughInjectives CategoryInjectiveResolution CategoryInjectiveResolutionComparison
  CategoryResolutionLimitMaps CategoryDerivedLimits HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalDiagramInjectives HomologicalDiagramLimits
  MackeyModuleQuotient ModuleInfrastructure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.
Local Opaque module_quotient linear_preimage linear_kernel linear_image
  chosen_injective_resolution injective_resolution_comparison.

Section ExtLimit.
Variable R : comPzRingType.
Variable C : category.

Definition constant_hom_limit_term_iso (K : @diagram_complex R C) n :
    @isomorphism (module_category R)
      (cochain_term (diagram_hom_complex (constant_regular_diagram R C) K) n)
      (cochain_term (limit_complex K) n) := constant_hom_limit_iso (diagram_term K n).

Lemma constant_hom_limit_term_commutes (K : @diagram_complex R C) n
    (v : cochain_term (diagram_hom_complex (constant_regular_diagram R C) K) n) :
    cochain_d (limit_complex K) n (module_hom_fun (iso_hom (constant_hom_limit_term_iso K n)) v) =
      module_hom_fun (iso_hom (constant_hom_limit_term_iso K n.+1))
        (cochain_d (diagram_hom_complex (constant_regular_diagram R C) K) n v).
Proof. symmetry; exact: constant_hom_limit_naturality. Qed.
Arguments constant_hom_limit_term_commutes K n v : clear implicits.

Definition constant_hom_limit_cochain_map (K : @diagram_complex R C) :
    cochain_map (diagram_hom_complex (constant_regular_diagram R C) K) (limit_complex K) :=
  term_iso_cochain_map (constant_hom_limit_term_commutes K).

Definition constant_ext_derived_limit_iso (D : module_diagram R C) n :
    @isomorphism (module_category R)
      (diagram_ext R (constant_regular_diagram R C) D n) (derived_limit R D n) :=
  term_iso_cohomology_iso
    (constant_hom_limit_term_commutes (injective_resolution_complex (chosen_injective_resolution R D))) n.

Lemma constant_ext_derived_limit_naturality {D E : module_diagram R C} (u : nat_trans D E) n :
    module_hom_comp (diagram_ext_map R (constant_regular_diagram R C) u n)
      (iso_hom (constant_ext_derived_limit_iso E n)) =
    module_hom_comp (iso_hom (constant_ext_derived_limit_iso D n)) (derived_limit_map R u n).
Proof.
apply module_hom_ext; intro q.
set (m := resolution_map_complex (injective_resolution_comparison
  (chosen_injective_resolution R D) (chosen_injective_resolution R E) u)).
change (cohomology_map (constant_hom_limit_cochain_map
    (injective_resolution_complex (chosen_injective_resolution R E))) n
    (cohomology_map (diagram_hom_cochain_map (constant_regular_diagram R C) m) n q) =
  cohomology_map (limit_cochain_map m) n
    (cohomology_map (constant_hom_limit_cochain_map
      (injective_resolution_complex (chosen_injective_resolution R D))) n q)).
apply cohomology_map_square.
intros k v; exact: constant_hom_limit_naturality.
Qed.

Definition constant_ext_derived_limit_nat_iso n :
    @isomorphism (functor_category (functor_category C (module_category R)) (module_category R))
      (@diagram_ext_functor R C (constant_regular_diagram R C) n) (derived_limit_functor R C n).
Proof.
refine (@nat_iso_of_components (functor_category C (module_category R)) (module_category R)
  (@diagram_ext_functor R C (constant_regular_diagram R C) n) (derived_limit_functor R C n)
  (fun D => constant_ext_derived_limit_iso D n) _).
intros D E u; exact: constant_ext_derived_limit_naturality.
Defined.
End ExtLimit.

