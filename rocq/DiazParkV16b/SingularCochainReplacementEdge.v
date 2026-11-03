(** Literal singular-cochain specialization of the native elementary
    replacement edge. Geometric realization comparison is not assumed here. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical.
From mathcomp Require Import reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryModules CategoryModuleLinear
  CategoryModuleExactness CategoryModuleLimits CategoryModuleLimitFunctor
  HomologicalComplex HomologicalMaps HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  CategoryComplexIso CategoryFiberVanishing
  HomologicalDiagramLimits CategoryDerivedLimits ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import TopologicalCategory SingularSet SingularCohomology
  SingularCohomologyFunctor SingularCochainDiagrams CochainMapsLaws
  CategoryCochainCohomologyDiagram CategoryCochainReplacementTotal
  CategoryCochainReplacementAcyclic CategoryCochainReplacementEdge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DPTopological DPSingularCohomology DPSingularCohomologyFunctor
  DPSingularCochainDiagrams DPCochainMapsLaws.
Local Open Scope ring_scope.

Module DPSingularReplacementEdge.
Section Singular.
Variable Real : realType.
Variable R : pzRingType.
Variable A : lmodType R.
Variable C : category.
Variable X : functor C topological_category.

Definition singular_cohomology_diagram n : module_codiagram R C :=
  functor_comp (functor_op X) (singular_cohomology_functor Real A n).

Definition singular_evaluation_term_iso c n : @isomorphism (module_category R)
    (cochain_term (diagram_evaluation_complex (singular_cochain_diagram Real A X) c) n)
    (cochain_term (singular_cochains Real (fobj X c) A) n) :=
  @iso_refl (module_category R) (cochain_term (singular_cochains Real (fobj X c) A) n).

Lemma singular_evaluation_term_commutes c n x :
    cochain_d (singular_cochains Real (fobj X c) A) n
      (module_hom_fun (iso_hom (singular_evaluation_term_iso c n)) x) =
    module_hom_fun (iso_hom (singular_evaluation_term_iso c n.+1))
      (cochain_d (diagram_evaluation_complex (singular_cochain_diagram Real A X) c) n x).
Proof. reflexivity. Qed.

Definition singular_evaluation_cochain_map c :=
  term_iso_cochain_map (@singular_evaluation_term_commutes c).

Definition singular_evaluation_cohomology_iso c n :=
  term_iso_cohomology_iso (@singular_evaluation_term_commutes c) n.

Definition singular_replacement_cohomology_iso n :
    @isomorphism (functor_category (opposite C) (module_category R))
      (cochain_cohomology_diagram (singular_cochain_diagram Real A X) n)
      (singular_cohomology_diagram n).
Proof.
refine (@nat_iso_of_components (opposite C) (module_category R)
  (cochain_cohomology_diagram (singular_cochain_diagram Real A X) n)
  (singular_cohomology_diagram n) (fun c => singular_evaluation_cohomology_iso c n) _).
intros c d f; apply module_hom_ext; intro a.
change (cohomology_map (singular_evaluation_cochain_map d) n
    (cohomology_map (diagram_evaluation_arrow (singular_cochain_diagram Real A X) f) n a) =
  singular_cohomology_map Real (fmap X f) A n (cohomology_map (singular_evaluation_cochain_map c) n a)).
apply cohomology_map_square; intros k z; reflexivity.
Defined.

Theorem singular_replacement_cohomology_iso_component n c
    (x : cohomology (diagram_evaluation_complex (singular_cochain_diagram Real A X) c) n) :
    module_hom_fun (component (iso_hom (singular_replacement_cohomology_iso n)) c) x =
      cohomology_map (singular_evaluation_cochain_map c) n x.
Proof. reflexivity. Qed.

Definition singular_replacement_total : cochain_complex R :=
  cochain_replacement_total (singular_cochain_diagram Real A X).

Definition singular_replacement_projection c :
    cochain_map singular_replacement_total (singular_cochains Real (fobj X c) A) :=
  cochain_composition (replacement_projection (singular_cochain_diagram Real A X) c)
    (singular_evaluation_cochain_map c).

Definition singular_positive_limits_vanish : Prop :=
  forall n p (x : derived_limit R (singular_cohomology_diagram n) p.+1), x = 0.

Lemma singular_replacement_positive_limits (hX : singular_positive_limits_vanish) :
    replacement_positive_limits_vanish (singular_cochain_diagram Real A X).
Proof.
intros n p x.
pose e := functor_iso (derived_limit_functor R (opposite C) p.+1)
  (singular_replacement_cohomology_iso n).
apply (module_iso_hom_injective (e := e)).
rewrite module_hom_zero. exact: hX.
Qed.

Definition singular_replacement_limit_iso (hX : singular_positive_limits_vanish) n :
    @isomorphism (module_category R) (cohomology singular_replacement_total n)
      (module_limit_type (singular_cohomology_diagram n)) :=
  module_iso_comp (replacement_total_limit_iso n (singular_replacement_positive_limits hX))
    (functor_iso (module_limit_functor R (opposite C)) (singular_replacement_cohomology_iso n)).

Theorem singular_replacement_limit_iso_component (hX : singular_positive_limits_vanish) n
    (x : cohomology singular_replacement_total n) c :
    module_limit_val (module_hom_fun (iso_hom (singular_replacement_limit_iso hX n)) x) c =
      cohomology_map (singular_replacement_projection c) n x.
Proof.
change (module_limit_val (limit_action (iso_hom (singular_replacement_cohomology_iso n))
  (module_hom_fun (iso_hom (replacement_total_limit_iso n (singular_replacement_positive_limits hX))) x)) c =
  cohomology_map (singular_replacement_projection c) n x).
rewrite limit_action_coordinate singular_replacement_cohomology_iso_component.
rewrite replacement_total_limit_iso_component.
symmetry; exact: cohomology_map_composition.
Qed.
End Singular.
End DPSingularReplacementEdge.
