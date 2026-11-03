(** The degree-zero identification uses precisely the augmentation and is
    natural for every comparison map, independently of its chosen lift. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryModuleLimits CategoryModuleExactness ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex
  HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  HomologicalDiagramInjectives HomologicalDiagramLimits
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison
  CategoryResolutionLimitMaps BarInjectiveDegreeZero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DiazParkBarInjectiveDegreeZero.
Local Open Scope ring_scope.

Module DiazParkBarInjectiveDegreeZeroNaturality.
Section Naturality.
Variable R : pzRingType.
Variable C : category.
Variables D E : module_diagram R C.
Variable J : injective_resolution D.
Let L := limit_complex (injective_resolution_complex J).

Lemma injective_degree_zero_inverse_pi (z : cycle_module L 0) :
    module_hom_fun (iso_inv (injective_degree_zero_iso J))
      (quotient_pi (boundaries_in_cycles L 0) z) = zero_cycle_limit J z.
Proof. exact: quotient_iso_map_pi. Qed.

Lemma injective_degree_zero_augmentation (v : module_limit_type D) :
    module_hom_fun (iso_hom (injective_degree_zero_iso J)) v =
      quotient_pi (boundaries_in_cycles L 0) (zero_limit_cycle J v).
Proof.
apply (@module_iso_hom_injective R _ _ (iso_symm (injective_degree_zero_iso J))).
change (module_hom_fun (iso_inv (injective_degree_zero_iso J))
  (module_hom_fun (iso_hom (injective_degree_zero_iso J)) v) =
  module_hom_fun (iso_inv (injective_degree_zero_iso J))
    (quotient_pi (boundaries_in_cycles L 0) (zero_limit_cycle J v))).
rewrite module_iso_hom_inv_apply injective_degree_zero_inverse_pi zero_cycle_limit_inverse.
reflexivity.
Qed.

End Naturality.
Section ComparisonNaturality.
Variable R : pzRingType.
Variable C : category.
Variables D E : module_diagram R C.
Variable J : injective_resolution D.
Variable J' : injective_resolution E.
Variable u : nat_trans D E.
Variable m : injective_resolution_map J J' u.

Theorem injective_degree_zero_naturality (v : module_limit_type D) :
    cohomology_map (limit_cochain_map (resolution_map_complex m)) 0
      (module_hom_fun (iso_hom (injective_degree_zero_iso J)) v) =
    module_hom_fun (iso_hom (injective_degree_zero_iso J')) (limit_action u v).
Proof.
rewrite !injective_degree_zero_augmentation cohomology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective.
apply module_limit_val_injective; apply functional_extensionality_dep; intro x.
change (module_limit_val (limit_action
  (diagram_cochain_map_at (resolution_map_complex m) 0)
  (limit_action (injective_resolution_augmentation J) v)) x =
  module_limit_val (limit_action (injective_resolution_augmentation J') (limit_action u v)) x).
rewrite !limit_action_coordinate.
exact (congr1 (fun t : nat_trans D (diagram_term (injective_resolution_complex J') 0) =>
  module_hom_fun (component t x) (module_limit_val v x)) (resolution_map_augmentation m)).
Qed.
End ComparisonNaturality.
End DiazParkBarInjectiveDegreeZeroNaturality.

