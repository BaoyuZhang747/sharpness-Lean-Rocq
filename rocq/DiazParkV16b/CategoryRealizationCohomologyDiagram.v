(** Unconditional, genuinely natural cohomology comparison for the actual
    realized costructured-category diagram of every functor. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryComma CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryDerivedLimits HomologicalCohomologyMaps.
From DiazParkV16b Require Import TopologicalCategory SingularCohomology SingularCochainReplacementEdge
  CategoryNerve CategoryConstantCohomology CategoryCostructuredDiagram CategoryCostructuredCohomologyDiagram
  GeometricRealizationMaps RealizationNerveCohomology RealizationNerveCohomologyUnconditional
  CategoryRealizationDecomposition.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPTopological DPSingularCohomology DPSingularReplacementEdge DPCategoryNerve
  DPCategoryCostructuredDiagram DPGeometricRealizationMaps DPRealizationNerveCohomology
  DPRealizationNerveCohomologyUnconditional DPCategoryRealizationDecomposition.

Module DPCategoryRealizationCohomologyDiagram.
Section Diagram.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variables C D : category.
Variable T : functor C D.
Variable n : nat.
Let SC := singular_cohomology_diagram Real A (space_diagram Real T) n.
Let CC := @DPCategoryCostructuredCohomologyDiagram.coefficient R A C D T n.

Definition comparison_object_iso (d : D) : @isomorphism (module_category R)
    (fobj SC d) (fobj CC d) :=
  comparison_iso_unconditional Real A (costructured_category T d) n.
Theorem comparison_object_naturality (d e : D) (f : hom D d e) :
  module_hom_comp (@fmap _ _ SC e d f) (iso_hom (comparison_object_iso d)) =
    module_hom_comp (iso_hom (comparison_object_iso e)) (@fmap _ _ CC e d f).
Proof.
apply module_hom_ext => x.
change (module_hom_fun (iso_hom (comparison_iso_unconditional Real A (costructured_category T d) n))
  (singular_cohomology_map Real (realization_map Real (nerve_map (reindex T f))) A n x) =
  module_hom_fun (DPCategoryConstantCohomology.pull A (reindex T f) n)
    (module_hom_fun (iso_hom (comparison_iso_unconditional Real A (costructured_category T e) n)) x)).
exact: comparison_iso_unconditional_natural.
Qed.
Definition comparison_nat_iso : @isomorphism (functor_category (opposite D) (module_category R)) SC CC :=
  @nat_iso_of_components (opposite D) (module_category R) SC CC comparison_object_iso
    (fun d e f => @comparison_object_naturality e d f).
Theorem comparison_nat_iso_component d :
  component (iso_hom comparison_nat_iso) d = iso_hom (comparison_object_iso d).
Proof. reflexivity. Qed.
Definition higher_limit_iso j : @isomorphism (module_category R)
    (derived_limit R SC j) (derived_limit R CC j) :=
  functor_iso (derived_limit_functor R (opposite D) j) comparison_nat_iso.
Theorem higher_limit_iso_hom j :
  iso_hom (higher_limit_iso j) = derived_limit_map R (iso_hom comparison_nat_iso) j.
Proof. reflexivity. Qed.
End Diagram.

(** Composition in the actual functor category, with both inverse laws. *)
Definition diagram_iso_comp {R : pzRingType} {C : category}
    {F G H : module_diagram R C}
    (e : @isomorphism (functor_category C (module_category R)) F G)
    (f : @isomorphism (functor_category C (module_category R)) G H) :
    @isomorphism (functor_category C (module_category R)) F H.
Proof.
refine (@Build_isomorphism (functor_category C (module_category R)) F H
  (nat_comp (iso_hom e) (iso_hom f)) (nat_comp (iso_inv f) (iso_inv e)) _ _).
- change (@compose (functor_category C (module_category R)) _ _ _
    (compose (iso_hom e) (iso_hom f)) (compose (iso_inv f) (iso_inv e)) =
      @identity (functor_category C (module_category R)) F).
  by rewrite compose_assoc -(compose_assoc (iso_hom f) (iso_inv f) (iso_inv e))
    (iso_hom_inv f) compose_id_left (iso_hom_inv e).
- change (@compose (functor_category C (module_category R)) _ _ _
    (compose (iso_inv f) (iso_inv e)) (compose (iso_hom e) (iso_hom f)) =
      @identity (functor_category C (module_category R)) H).
  by rewrite compose_assoc -(compose_assoc (iso_inv e) (iso_hom e) (iso_hom f))
    (iso_inv_hom e) compose_id_left (iso_inv_hom f).
Defined.
End DPCategoryRealizationCohomologyDiagram.
