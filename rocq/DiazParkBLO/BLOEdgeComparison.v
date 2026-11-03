(** An actual cocone cochain augmentation and its elementary edge.
    This general comparison lemma is conditional on a separately proved
    canonical isomorphism and its component formula. The BLO endpoint must
    construct those inputs; no centraliser sharpness premise is introduced. *)
From mathcomp Require Import all_ssreflect all_algebra all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  CategoryModuleExactness HomologicalComplex HomologicalCohomology
  HomologicalCohomologyMaps HomologicalModuleIso MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import TopologicalCategory SingularCohomology
  SimplicialReplacementConstants SingularCochainReplacementEdge
  SingularReplacementGeometricComparison.
Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPTopological DPSingularCohomology DPSimplicialReplacementConstants
  DPSingularReplacementEdge DPSingularReplacementGeometricComparison
  DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso.

Module DPBLOEdgeComparison.
Section Cocone.
Variable Real : realType.
Variable R : comPzRingType.
Variable A : lmodType R.
Variable I : category.
Variable D : functor I topological_category.
Variable Y : topologicalType.
Variable a : nat_trans D (@constant_diagram I topological_category Y).

Definition augmentation : cochain_map (singular_cochains Real Y A)
    (singular_replacement_total Real A D) :=
  singular_geometric_comparison Real A a.

Theorem augmentation_cochain_component n z i :
  cochain_map_at (singular_replacement_projection Real A D i) n
    (cochain_map_at augmentation n z) =
  cochain_map_at (singular_pullback Real (component a i) A) n z.
Proof. exact: singular_geometric_comparison_restriction. Qed.

Theorem augmentation_cohomology_component n z i :
  cohomology_map (singular_replacement_projection Real A D i) n
    (cohomology_map augmentation n z) =
  singular_cohomology_map Real (component a i) A n z.
Proof. exact: singular_geometric_cohomology_restriction. Qed.

Variable hD : singular_positive_limits_vanish Real A D.

(** This is the actual composite edge, before any augmentation-isomorphism
    claim: cohomology of the cocone map followed by the elementary edge. *)
Definition edge n (z : singular_cohomology Real Y A n) :=
  module_hom_fun (iso_hom (singular_replacement_limit_iso hD n))
    (cohomology_map augmentation n z).
Arguments edge n z : clear implicits.

Theorem edge_component n z i :
  module_limit_val (edge n z) i =
  singular_cohomology_map Real (component a i) A n z.
Proof.
rewrite /edge singular_replacement_limit_iso_component.
exact: augmentation_cohomology_component.
Qed.

(** Generic cancellation interface. These data will be supplied by actual
    subgroup stable elements, the canonical ordinary E3 comparison, and the
    proved BLO natural isomorphism, not assumed by a manuscript-facing result. *)
Variable canonical : forall n, @isomorphism (module_category R)
  [the lmodType R of singular_cohomology Real Y A n]
  (module_limit_type (singular_cohomology_diagram Real A D n)).
Hypothesis canonical_component : forall n z i,
  module_limit_val (module_hom_fun (iso_hom (canonical n)) z) i =
  singular_cohomology_map Real (component a i) A n z.

Theorem edge_is_canonical n z :
  edge n z = module_hom_fun (iso_hom (canonical n)) z.
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep => i.
by rewrite edge_component canonical_component.
Qed.

Definition augmentation_cohomology_iso n : @isomorphism (module_category R)
  [the lmodType R of singular_cohomology Real Y A n]
  (cohomology (singular_replacement_total Real A D) n) :=
  module_iso_comp (canonical n) (iso_symm (singular_replacement_limit_iso hD n)).

Theorem augmentation_cohomology_iso_hom n z :
  module_hom_fun (iso_hom (augmentation_cohomology_iso n)) z =
  cohomology_map augmentation n z.
Proof.
apply (module_iso_hom_injective (e := singular_replacement_limit_iso hD n)).
change (module_hom_fun (iso_hom (singular_replacement_limit_iso hD n))
  (module_hom_fun (iso_inv (singular_replacement_limit_iso hD n))
    (module_hom_fun (iso_hom (canonical n)) z)) = edge n z).
rewrite module_iso_inv_hom_apply; symmetry; exact: edge_is_canonical.
Qed.

(** A cochain quasi-isomorphism means precisely that this actual cochain
    map induces bijections on cohomology in every nonnegative degree. *)
Theorem augmentation_cochain_quasi_isomorphism :
  forall n, bijective (cohomology_map augmentation n).
Proof.
move=> n.
exists (module_hom_fun (iso_inv (augmentation_cohomology_iso n))).
- move=> z; rewrite -augmentation_cohomology_iso_hom.
  exact: module_iso_hom_inv_apply.
- move=> z; rewrite -augmentation_cohomology_iso_hom.
  exact: module_iso_inv_hom_apply.
Qed.

Theorem edge_bijective n : bijective (edge n).
Proof.
exists (module_hom_fun (iso_inv (canonical n))).
- move=> z; rewrite edge_is_canonical; exact: module_iso_hom_inv_apply.
- move=> z; rewrite edge_is_canonical; exact: module_iso_inv_hom_apply.
Qed.
End Cocone.
End DPBLOEdgeComparison.
