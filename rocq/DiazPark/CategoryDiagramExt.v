(** Ext is independently defined as actual quotient cohomology of Hom(A,J),
    where J is the constructed injective resolution of the second argument. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryDiagramHom CategoryDiagramHomComplex CategoryEnoughInjectives
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison
  CategoryDerivedLimits HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalDiagramInjectives
  MackeyModuleCarriers MackeyModuleQuotient ModuleInfrastructure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.
Local Open Scope ring_scope.
Local Opaque chosen_injective_resolution injective_resolution_comparison module_quotient linear_preimage linear_kernel linear_image.
Section DiagramExt.
Variable R : comPzRingType.
Variable C : category.
Variable A : module_diagram R C.

Definition diagram_ext (F : module_diagram R C) n : lmodType R :=
  [the lmodType R of cohomology
    (diagram_hom_complex A (injective_resolution_complex (chosen_injective_resolution R F))) n].

Definition diagram_ext_map {F G : module_diagram R C} (u : nat_trans F G) n :
    module_hom (diagram_ext F n) (diagram_ext G n) :=
  module_hom_of_linear (cohomology_map
    (diagram_hom_cochain_map A (resolution_map_complex
      (injective_resolution_comparison (chosen_injective_resolution R F)
        (chosen_injective_resolution R G) u))) n).

Lemma diagram_ext_map_identity (F : module_diagram R C) n :
    diagram_ext_map (nat_id F) n = module_hom_id (diagram_ext F n).
Proof.
apply module_hom_ext; intro q.
change (cohomology_map (diagram_hom_cochain_map A (resolution_map_complex
  (injective_resolution_comparison (chosen_injective_resolution R F)
    (chosen_injective_resolution R F) (nat_id F)))) n q = q).
rewrite (diagram_hom_resolution_map_independent
  (injective_resolution_comparison (chosen_injective_resolution R F)
    (chosen_injective_resolution R F) (nat_id F))
  (injective_resolution_identity (chosen_injective_resolution R F)) q).
exact: diagram_hom_cohomology_identity.
Qed.

Lemma diagram_ext_map_composition {F G H : module_diagram R C}
    (u : nat_trans F G) (v : nat_trans G H) n :
    diagram_ext_map (nat_comp u v) n =
      module_hom_comp (diagram_ext_map u n) (diagram_ext_map v n).
Proof.
apply module_hom_ext; intro q.
change (cohomology_map (diagram_hom_cochain_map A (resolution_map_complex
  (injective_resolution_comparison (chosen_injective_resolution R F)
    (chosen_injective_resolution R H) (nat_comp u v)))) n q =
  cohomology_map (diagram_hom_cochain_map A (resolution_map_complex
    (injective_resolution_comparison (chosen_injective_resolution R G)
      (chosen_injective_resolution R H) v))) n
  (cohomology_map (diagram_hom_cochain_map A (resolution_map_complex
    (injective_resolution_comparison (chosen_injective_resolution R F)
      (chosen_injective_resolution R G) u))) n q)).
transitivity (cohomology_map (diagram_hom_cochain_map A (resolution_map_complex
  (injective_resolution_composition
    (injective_resolution_comparison (chosen_injective_resolution R F)
      (chosen_injective_resolution R G) u)
    (injective_resolution_comparison (chosen_injective_resolution R G)
      (chosen_injective_resolution R H) v)))) n q).
- exact: diagram_hom_resolution_map_independent.
- exact: diagram_hom_cohomology_composition.
Qed.

Definition diagram_ext_functor (n : nat) :
    functor (functor_category C (module_category R)) (module_category R).
Proof.
refine (@Build_functor (functor_category C (module_category R)) (module_category R)
  (fun F => diagram_ext F n) (fun F G u => diagram_ext_map u n) _ _).
- intro F; exact: diagram_ext_map_identity.
- intros F G H u v; exact: diagram_ext_map_composition.
Defined.
End DiagramExt.

Arguments diagram_ext R {C} A F n.
Arguments diagram_ext_map R {C} A {F G} u n.
Arguments diagram_ext_functor R C A n.






