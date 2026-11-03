(** The vertical-cohomology comparison intertwines the actual horizontal
    map with the literal category-bar differential, including all signs. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  HomologicalComplex HomologicalDiagramInjectives CategoryFiberVanishing
  HomologicalCohomology HomologicalCohomologyMaps ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient BarPaths BarComplex BarNaturality.
From DiazParkV16b Require Import FirstQuadrantCochainEdge CategoryCochainReplacement
  CategoryCochainReplacementVertical CategoryCochainCycleDiagram CategoryCochainCohomologyDiagram.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkBarPaths DiazParkBarComplex DiazParkBarNaturality DPFirstQuadrantEdge.
Local Open Scope ring_scope.

Section Horizontal.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R (opposite C).
Variable q : nat.

Definition replacement_cycles_to_bar p (z : cycle_module (replacement_column K p) q) :
    bar_term (cochain_cycle_diagram K q) p :=
  fun c s => cycle_map (replacement_column_projection K s) q z.

Lemma cycle_bar_inclusion_injective p :
    injective (@bar_map_at R C _ _ (cochain_cycle_inclusion K q) p).
Proof.
intros a b h; apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intro s; apply submodule_val_injective.
exact (f_equal (fun v : bar_term (diagram_term K q) p => v c s) h).
Qed.

Lemma replacement_cycles_to_bar_horizontal p (z : cycle_module (replacement_column K p) q) :
    replacement_cycles_to_bar
      (cycle_map (horizontal_column_map (cochain_replacement_bicomplex K) p) q z) =
    bar_d (cochain_cycle_diagram K q) p (replacement_cycles_to_bar z).
Proof.
apply (@cycle_bar_inclusion_injective p.+1).
change (bar_d (diagram_term K q) p (cycle_inclusion (replacement_column K p) q z) =
  bar_map_at (cochain_cycle_inclusion K q)
    (bar_d (cochain_cycle_diagram K q) p (replacement_cycles_to_bar z))).
rewrite <- bar_map_d. reflexivity.
Qed.

Lemma replacement_vertical_cohomology_cycle p (z : cycle_module (replacement_column K p) q) :
    module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K p q))
      (quotient_pi (boundaries_in_cycles (replacement_column K p) q) z) =
    bar_map_at (cochain_cycle_quotient K q) (replacement_cycles_to_bar z).
Proof.
apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intro s.
rewrite replacement_vertical_cohomology_component cohomology_map_pi.
reflexivity.
Qed.

Theorem replacement_vertical_cohomology_horizontal p (x : cohomology (replacement_column K p) q) :
    module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K p.+1 q))
      (horizontal_cohomology (cochain_replacement_bicomplex K) p q x) =
    bar_d (cochain_cohomology_diagram K q) p
      (module_hom_fun (iso_hom (replacement_vertical_cohomology_iso K p q)) x).
Proof.
have [z <-] := quotient_pi_surjective x.
rewrite /horizontal_cohomology cohomology_map_pi !replacement_vertical_cohomology_cycle
  replacement_cycles_to_bar_horizontal bar_map_d.
reflexivity.
Qed.
End Horizontal.
