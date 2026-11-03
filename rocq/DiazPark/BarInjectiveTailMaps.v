From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  ModuleInfrastructure MackeyModuleCarriers ModuleDiagrams HomologicalDiagramInjectives
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison BarInjectiveResolutionTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarInjectiveResolutionTail.
Local Open Scope ring_scope.

Module DiazParkBarInjectiveTailMaps.
Section Maps.
Variable R : pzRingType.
Variable C : category.
Variables D E : module_codiagram R C.
Variables (J : injective_resolution D) (J' : injective_resolution E).
Variable u : nat_trans D E.
Variable m : injective_resolution_map J J' u.
Let K := injective_resolution_complex J.
Let K' := injective_resolution_complex J'.
Let a := resolution_map_complex m.

Lemma syzygy_comparison_kernel x (z : fobj (injective_syzygy J) x) :
  module_hom_fun (component (diagram_d K' 1) x)
    (module_hom_fun (component (diagram_cochain_map_at a 1) x) (submodule_val z)) = 0.
Proof.
rewrite (diagram_cochain_map_commutes a 1 x) (submodule_val_mem z).
exact: module_hom_zero.
Qed.

Definition syzygy_comparison_component x :
    module_hom (fobj (injective_syzygy J) x) (fobj (injective_syzygy J') x).
Proof.
refine (exist _ (fun z => @submodule_in R (fobj (diagram_term K' 1) x)
  (diagram_kernel_subspace (diagram_d K' 1) x)
  (module_hom_fun (component (diagram_cochain_map_at a 1) x) (submodule_val z))
  (syzygy_comparison_kernel z)) _).
move=> r v w; apply submodule_val_injective.
exact: module_hom_linear.
Defined.

Definition syzygy_comparison : nat_trans (injective_syzygy J) (injective_syzygy J').
Proof.
refine (@Build_nat_trans (opposite C) (module_category R)
  (injective_syzygy J) (injective_syzygy J') syzygy_comparison_component _).
move=> x y f; apply module_hom_ext => z; apply submodule_val_injective.
exact: (congr1 (fun k => module_hom_fun k (submodule_val z))
  (naturality (diagram_cochain_map_at a 1) f)).
Defined.

Lemma syzygy_comparison_val x (z : fobj (injective_syzygy J) x) :
  submodule_val (module_hom_fun (component syzygy_comparison x) z) =
  module_hom_fun (component (diagram_cochain_map_at a 1) x) (submodule_val z).
Proof. reflexivity. Qed.

Lemma syzygy_comparison_square x (v : fobj (diagram_term K 0) x) :
  module_hom_fun (component (injective_syzygy_map J') x)
    (module_hom_fun (component (diagram_cochain_map_at a 0) x) v) =
  module_hom_fun (component syzygy_comparison x)
    (module_hom_fun (component (injective_syzygy_map J) x) v).
Proof.
apply submodule_val_injective; exact: diagram_cochain_map_commutes.
Qed.

Definition injective_tail_complex_map :
    diagram_cochain_map (injective_tail_complex J) (injective_tail_complex J') :=
  @Build_diagram_cochain_map R (opposite C) (injective_tail_complex J) (injective_tail_complex J')
    (fun n => diagram_cochain_map_at a n.+1) (fun n => diagram_cochain_map_commutes a n.+1).

Definition injective_tail_resolution_map :
    injective_resolution_map (injective_tail_resolution J) (injective_tail_resolution J')
      syzygy_comparison.
Proof.
refine (@Build_injective_resolution_map R (opposite C) (injective_syzygy J) (injective_syzygy J')
  (injective_tail_resolution J) (injective_tail_resolution J') syzygy_comparison
  injective_tail_complex_map _).
apply nat_trans_ext => x; apply module_hom_ext => z; reflexivity.
Defined.

End Maps.
End DiazParkBarInjectiveTailMaps.
