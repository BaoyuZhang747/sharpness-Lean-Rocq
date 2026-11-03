(** Literal native cycle modules form a diagram, with the actual inclusion
    and cycle-to-cohomology quotient natural transformations. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  HomologicalComplex HomologicalDiagramInjectives CategoryFiberVanishing
  HomologicalCohomology HomologicalCohomologyMaps ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient.
From DiazParkV16b Require Import CategoryCochainCohomologyDiagram.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps.

Section Cycles.
Variable R : pzRingType.
Variable C : category.
Variable K : @diagram_complex R C.
Variable q : nat.

Definition cochain_cycle_diagram : module_diagram R C.
Proof.
refine (@Build_functor C (module_category R)
  (fun c => [the lmodType R of cycle_module (diagram_evaluation_complex K c) q])
  (fun c d f => module_hom_of_linear (cycle_map (diagram_evaluation_arrow K f) q)) _ _).
- intro c; apply module_hom_ext; intro x; apply submodule_val_injective.
  change (module_hom_fun (fmap (diagram_term K q) (identity c)) (submodule_val x) = submodule_val x).
  by rewrite fmap_id.
- intros c d e f g; apply module_hom_ext; intro x; apply submodule_val_injective.
  change (module_hom_fun (fmap (diagram_term K q) (compose f g)) (submodule_val x) =
    module_hom_fun (fmap (diagram_term K q) g) (module_hom_fun (fmap (diagram_term K q) f) (submodule_val x))).
  by rewrite fmap_compose.
Defined.

Definition cochain_cycle_inclusion : nat_trans cochain_cycle_diagram (diagram_term K q).
Proof.
refine (@Build_nat_trans C (module_category R) cochain_cycle_diagram (diagram_term K q)
  (fun c => module_hom_of_linear (cycle_inclusion (diagram_evaluation_complex K c) q)) _).
intros c d f; apply module_hom_ext; intro x; reflexivity.
Defined.

Definition cochain_cycle_quotient : nat_trans cochain_cycle_diagram (cochain_cohomology_diagram K q).
Proof.
refine (@Build_nat_trans C (module_category R) cochain_cycle_diagram (cochain_cohomology_diagram K q)
  (fun c => module_hom_of_linear
    (quotient_pi (boundaries_in_cycles (diagram_evaluation_complex K c) q) : {linear _ -> _})) _).
intros c d f; apply module_hom_ext; intro x.
symmetry; exact: cohomology_map_pi.
Defined.
End Cycles.
