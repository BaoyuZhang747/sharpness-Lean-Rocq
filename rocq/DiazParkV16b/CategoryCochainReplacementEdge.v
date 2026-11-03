(** The actual all-degree replacement edge to the ordinary limit of the
    cohomology diagram, with every component equal to the native projection. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleExactness
  CategoryModuleLimits HomologicalComplex HomologicalDiagramInjectives CategoryFiberVanishing
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient BarComplex BarDegreeZero.
From DiazParkV16b Require Import CochainMapsLaws FirstQuadrantCochainEdge
  FirstQuadrantCochainEdgeComparison FirstQuadrantCochainTotalMaps
  CategoryCochainReplacement CategoryCochainReplacementTotal CategoryCochainCohomologyDiagram
  CategoryCochainReplacementVertical CategoryCochainReplacementHorizontal CategoryCochainReplacementAcyclic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DiazParkBarComplex DiazParkBarDegreeZero DPCochainMapsLaws
  DPFirstQuadrantEdge DPFirstQuadrantEdgeComparison DPFirstQuadrantTotalMaps.
Local Open Scope ring_scope.

Section LimitEdge.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).
Variable n : nat.

Definition replacement_edge_to_cycle_fun (a : edge_module (cochain_replacement_bicomplex K) n) :
    cycle_module (bar_complex (cochain_cohomology_diagram K n)) 0%N.
Proof.
refine (@cycle_of_cocycle R (bar_complex (cochain_cohomology_diagram K n)) 0%N
  (module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K 0%N n)) (submodule_val a)) _).
change (bar_d (cochain_cohomology_diagram K n) 0%N
  (module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K 0%N n)) (submodule_val a)) = 0).
rewrite -replacement_vertical_cohomology_horizontal (submodule_val_mem a) module_hom_zero.
reflexivity.
Defined.

Definition replacement_edge_to_cycle : module_hom
    (edge_module (cochain_replacement_bicomplex K) n)
    [the lmodType R of cycle_module (bar_complex (cochain_cohomology_diagram K n)) 0%N].
Proof.
exists replacement_edge_to_cycle_fun; intros r a b; apply submodule_val_injective.
change (module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K 0%N n))
  (r *: submodule_val a + submodule_val b) =
  r *: module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K 0%N n)) (submodule_val a) +
  module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K 0%N n)) (submodule_val b)).
exact: module_hom_linear.
Defined.

Definition replacement_cycle_to_edge_fun
    (z : cycle_module (bar_complex (cochain_cohomology_diagram K n)) 0%N) :
    edge_module (cochain_replacement_bicomplex K) n.
Proof.
refine (@submodule_in R (cohomology (replacement_column K 0%N) n)
  (edge_kernel (cochain_replacement_bicomplex K) n)
  (module_hom_fun (iso_inv (replacement_vertical_cohomology_iso K 0%N n)) (submodule_val z)) _).
change (horizontal_cohomology (cochain_replacement_bicomplex K) 0%N n
  (module_hom_fun (iso_inv (replacement_vertical_cohomology_iso K 0%N n)) (submodule_val z)) = 0).
apply (module_iso_hom_injective (e := replacement_vertical_cohomology_iso K 1%N n)).
rewrite module_hom_zero replacement_vertical_cohomology_horizontal module_iso_inv_hom_apply.
exact (submodule_val_mem z).
Defined.

Definition replacement_cycle_to_edge : module_hom
    [the lmodType R of cycle_module (bar_complex (cochain_cohomology_diagram K n)) 0%N]
    (edge_module (cochain_replacement_bicomplex K) n).
Proof.
exists replacement_cycle_to_edge_fun; intros r a b; apply submodule_val_injective.
change (module_hom_fun (iso_inv (replacement_vertical_cohomology_iso K 0%N n))
  (r *: submodule_val a + submodule_val b) =
  r *: module_hom_fun (iso_inv (replacement_vertical_cohomology_iso K 0%N n)) (submodule_val a) +
  module_hom_fun (iso_inv (replacement_vertical_cohomology_iso K 0%N n)) (submodule_val b)).
exact: module_hom_linear.
Defined.

Definition replacement_edge_cycle_iso : @isomorphism (module_category R)
    (edge_module (cochain_replacement_bicomplex K) n)
    [the lmodType R of cycle_module (bar_complex (cochain_cohomology_diagram K n)) 0%N].
Proof.
refine (@Build_isomorphism (module_category R) _ _ replacement_edge_to_cycle replacement_cycle_to_edge _ _).
- apply module_hom_ext; intro a; apply submodule_val_injective.
  exact: module_iso_hom_inv_apply.
- apply module_hom_ext; intro a; apply submodule_val_injective.
  exact: module_iso_inv_hom_apply.
Defined.

Definition replacement_bar_cycle_limit_iso : @isomorphism (module_category R)
    [the lmodType R of cycle_module (bar_complex (cochain_cohomology_diagram K n)) 0%N]
    (module_limit_type (cochain_cohomology_diagram K n)).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (bar_cycle_to_limit (cochain_cohomology_diagram K n))
  (bar_limit_to_cycle (cochain_cohomology_diagram K n)) _ _).
- apply module_hom_ext; exact: bar_limit_cycle_inverse.
- apply module_hom_ext; exact: bar_cycle_limit_inverse.
Defined.

Definition replacement_edge_limit_iso : @isomorphism (module_category R)
    (edge_module (cochain_replacement_bicomplex K) n)
    (module_limit_type (cochain_cohomology_diagram K n)) :=
  module_iso_comp replacement_edge_cycle_iso replacement_bar_cycle_limit_iso.

Definition replacement_total_limit_iso (hK : replacement_positive_limits_vanish K) :
    @isomorphism (module_category R) (cohomology (cochain_replacement_total K) n)
      (module_limit_type (cochain_cohomology_diagram K n)) :=
  module_iso_comp (edge_iso (replacement_positive_horizontal_exact hK) n) replacement_edge_limit_iso.

Theorem replacement_total_limit_iso_component (hK : replacement_positive_limits_vanish K)
    (x : cohomology (cochain_replacement_total K) n) (c : C) :
    module_limit_val (module_hom_fun (iso_hom (replacement_total_limit_iso hK)) x) c =
      cohomology_map (replacement_projection K c) n x.
Proof.
change (module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K 0%N n))
  (cohomology_map (zero_column_projection (cochain_replacement_bicomplex K)) n x) c tt =
  cohomology_map (replacement_projection K c) n x).
rewrite replacement_vertical_cohomology_component.
symmetry; apply cohomology_composition_of; intro a; reflexivity.
Qed.
End LimitEdge.
