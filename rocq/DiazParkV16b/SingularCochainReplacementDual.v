(** Native Hom-dual and function-valued singular diagram replacements agree, including the edge. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear CategoryNaturalIso CategoryComplexIso
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalDiagramInjectives BarFreeModule.
From DiazParkV16b Require Import TopologicalCategory SingularSet SingularCohomology SingularCochainDiagrams
  SimplicialSet SimplicialSetYoneda SimplicialChains SimplicialChainsMaps SimplicialCochains SimplicialCochainQuasiIso
  ChainDualCochain LinearMapSpace GeometricRealizationSingularAdjunction CategoryCochainReplacementSimplicial
  CategoryCochainReplacementSimplicialEvaluation CategoryCochainReplacementTermIso
  CategoryCochainReplacementTotal SingularCochainReplacementEdge.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps DiazParkFreeModule
  DPTopological DPSingularSet DPSingularCohomology DPSingularCochainDiagrams DPSimplicialSet DPSimplicialYoneda
  DPSimplicialChains DPSimplicialChainMaps DPSimplicialCochains DPSimplicialCochainQuasiIso
  DPChainDualCochain DPLinearMapSpace DPGeometricRealizationSingularAdjunction
  DPCategoryCochainReplacementSimplicial DPCategoryCochainReplacementSimplicialEvaluation
  DPCategoryCochainReplacementTermIso DPSingularReplacementEdge.

Module DPSingularCochainReplacementDual.
Section Comparison.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable C : category.
Variable X : functor C topological_category.
Let F := functor_comp X (singular_functor Real).
Let K := dual_diagram F A.
Let L := singular_cochain_diagram Real A X.

Definition singular_dual_degree_iso n : @isomorphism (functor_category (opposite C) (module_category R))
  (diagram_term K n) (diagram_term L n).
Proof.
refine (@nat_iso_of_components (opposite C) (module_category R) (diagram_term K n) (diagram_term L n)
  (fun c => @dual_function_iso R (singular_set Real (fobj X c)) A n) _).
move=> c d f; apply module_hom_ext => z.
exact (@dual_functions_pull_square R A (singular_set Real (fobj X d))
  (singular_set Real (fobj X c)) (singular_map Real (fmap X f)) n z).
Defined.

Lemma singular_dual_differential n c (z : fobj (diagram_term K n) c) :
  module_hom_fun (component (diagram_d L n) c)
    (module_hom_fun (component (iso_hom (singular_dual_degree_iso n)) c) z) =
  module_hom_fun (component (iso_hom (singular_dual_degree_iso n.+1)) c)
    (module_hom_fun (component (diagram_d K n) c) z).
Proof. exact (@dual_function_differential R (singular_set Real (fobj X c)) A n z). Qed.

Definition singular_dual_diagram_map := @diagram_term_iso_map R C K L singular_dual_degree_iso singular_dual_differential.
Definition singular_dual_diagram_inverse := @diagram_term_iso_inverse R C K L singular_dual_degree_iso singular_dual_differential.
Definition singular_dual_total_cochain := @replacement_term_cochain R C K L singular_dual_degree_iso singular_dual_differential.
Definition singular_dual_total_inverse := @replacement_term_cochain_inverse R C K L singular_dual_degree_iso singular_dual_differential.
Definition singular_dual_total_cohomology_iso n :=
  @replacement_term_cohomology_iso R C K L singular_dual_degree_iso singular_dual_differential n.

Theorem singular_dual_total_left n z :
  cochain_map_at singular_dual_total_inverse n (cochain_map_at singular_dual_total_cochain n z)=z.
Proof. exact: replacement_term_cochain_left. Qed.
Theorem singular_dual_total_right n z :
  cochain_map_at singular_dual_total_cochain n (cochain_map_at singular_dual_total_inverse n z)=z.
Proof. exact: replacement_term_cochain_right. Qed.
Theorem singular_dual_total_component n z p q h c t s :
  cochain_map_at singular_dual_total_cochain n z p q h c t s =
  evaluate (z p q h c t) (free_basis R s).
Proof. reflexivity. Qed.

Theorem singular_dual_total_projection n z c :
  cochain_map_at (singular_replacement_projection Real A X c) n
    (cochain_map_at singular_dual_total_cochain n z) =
  cochain_map_at (dual_functions A (singular_set Real (fobj X c))) n
    (cochain_map_at (dual_replacement_projection F A c) n z).
Proof. reflexivity. Qed.
Theorem singular_dual_total_cohomology_projection n z c :
  cohomology_map (singular_replacement_projection Real A X c) n
    (cohomology_map singular_dual_total_cochain n z) =
  cohomology_map (dual_functions A (singular_set Real (fobj X c))) n
    (cohomology_map (dual_replacement_projection F A c) n z).
Proof. apply cohomology_map_square => k x; exact (@singular_dual_total_projection k x c). Qed.
Theorem singular_dual_total_cohomology_iso_hom n z :
  module_hom_fun (iso_hom (singular_dual_total_cohomology_iso n)) z =
  cohomology_map singular_dual_total_cochain n z.
Proof. reflexivity. Qed.
Theorem singular_dual_total_cohomology_iso_projection n z c :
  cohomology_map (singular_replacement_projection Real A X c) n
    (module_hom_fun (iso_hom (singular_dual_total_cohomology_iso n)) z) =
  cohomology_map (dual_functions A (singular_set Real (fobj X c))) n
    (cohomology_map (dual_replacement_projection F A c) n z).
Proof. exact: singular_dual_total_cohomology_projection. Qed.
End Comparison.
End DPSingularCochainReplacementDual.
