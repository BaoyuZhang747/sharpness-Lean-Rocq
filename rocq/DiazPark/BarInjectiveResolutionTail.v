From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryInjectives
  ModuleDiagrams ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalDiagramInjectives HomologicalDiagramLimits
  CategoryInjectiveResolution BarComplex BarNaturality BarExactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkBarComplex DiazParkBarNaturality DiazParkBarExactness.
Local Open Scope ring_scope.

Module DiazParkBarInjectiveResolutionTail.
Section Tail.
Variable R : pzRingType.
Variable C : category.
Variable D : module_codiagram R C.
Variable J : injective_resolution D.
Let K := injective_resolution_complex J.

Definition injective_syzygy : module_codiagram R C := diagram_cycles K 1.
Definition injective_syzygy_map : nat_trans (diagram_term K 0) injective_syzygy :=
  diagram_cycle_d K 0.

Lemma injective_syzygy_surjective x (v : fobj injective_syzygy x) :
  exists u, module_hom_fun (component injective_syzygy_map x) u = v.
Proof.
have [u hu] := injective_resolution_exact_successor J 0 x
  (submodule_val v) (submodule_val_mem v).
exists u; apply submodule_val_injective; exact: hu.
Qed.

Lemma injective_syzygy_kernel x (v : fobj (diagram_term K 0) x) :
  module_hom_fun (component injective_syzygy_map x) v = 0 ->
  exists u, module_hom_fun (component (injective_resolution_augmentation J) x) u = v.
Proof.
move=> hv; apply/(injective_resolution_exact_zero J x v).
exact: (congr1 (@submodule_val R (fobj (diagram_term K 1) x)
  (diagram_kernel_subspace (diagram_d K 1) x)) hv).
Qed.

Lemma injective_syzygy_composite x (v : fobj D x) :
  module_hom_fun (component injective_syzygy_map x)
    (module_hom_fun (component (injective_resolution_augmentation J) x) v) = 0.
Proof. apply submodule_val_injective; exact: injective_resolution_augmentation_zero. Qed.

Definition injective_syzygy_bar_short_exact :
  degreewise_short_exact (bar_cochain_map (injective_resolution_augmentation J))
    (bar_cochain_map injective_syzygy_map) :=
  @bar_short_exact R C D (diagram_term K 0) injective_syzygy
    (injective_resolution_augmentation J) injective_syzygy_map
    (injective_resolution_augmentation_injective J) injective_syzygy_composite
    injective_syzygy_kernel injective_syzygy_surjective.

Definition injective_tail_complex : @diagram_complex R (opposite C) :=
  @DiagramComplex R (opposite C) (fun n => diagram_term K n.+1)
    (fun n => diagram_d K n.+1) (fun n => @diagram_d2 R (opposite C) K n.+1).

Definition injective_tail_resolution : injective_resolution injective_syzygy.
Proof.
refine (@Build_injective_resolution R (opposite C) injective_syzygy injective_tail_complex
  (diagram_cycle_inclusion K 1) _ _ _ _ _).
- move=> n; exact: (injective_resolution_term_injective J n.+1).
- move=> x; exact: diagram_kernel_inclusion_injective.
- move=> x v; exact: (submodule_val_mem v).
- move=> x v; split.
  * move=> hv; exists (@submodule_in R (fobj (diagram_term K 1) x)
      (diagram_kernel_subspace (diagram_d K 1) x) v hv); reflexivity.
  * move=> [u <-]; exact: (submodule_val_mem u).
- move=> n x v hv; exact: (injective_resolution_exact_successor J n.+1 x v hv).
Defined.

(** Only positive degrees are shifted here; the new degree-zero boundary
    module is zero and must be handled separately. *)
Local Opaque module_quotient linear_preimage linear_kernel linear_image.
Definition injective_tail_cohomology_iso n : @isomorphism (module_category R)
    [the lmodType R of cohomology (limit_complex injective_tail_complex) n.+1]
    [the lmodType R of cohomology (limit_complex K) n.+2].
Proof.
cbv beta iota zeta delta [cohomology boundaries_in_cycles boundary_subspace cycle_module cycle_subspace cycle_inclusion injective_tail_complex limit_complex cochain_term cochain_d diagram_term diagram_d].
exact (@iso_refl (module_category R) [the lmodType R of cohomology (limit_complex K) n.+2]).
Defined.

End Tail.
End DiazParkBarInjectiveResolutionTail.




