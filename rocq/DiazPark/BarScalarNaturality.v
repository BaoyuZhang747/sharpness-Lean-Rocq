From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleExactness
  CategoryComplexIso HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalScalarRestriction HomologicalScalarCohomology HomologicalModuleIso
  BarComplex BarNaturality BarScalarComplex ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkScalarRestriction DiazParkScalarCohomology DiazParkHomologicalModuleIso
  DiazParkBarComplex DiazParkBarNaturality DiazParkBarScalarComplex.
Local Open Scope ring_scope.

Module DiazParkBarScalarNaturality.
Section Scalars.
Variables A B : pzRingType.
Variable f : {rmorphism A -> B}.
Variable C : category.
Local Opaque module_quotient linear_preimage linear_kernel linear_image.

Definition bar_scalar_cycle (D : module_codiagram B C) n (z : cycle_module (bar_complex D) n) :
    cycle_module (bar_complex (restriction_diagram f D)) n.
Proof.
apply (@cycle_of_cocycle A (bar_complex (restriction_diagram f D)) n (cycle_inclusion (bar_complex D) n z)).
change (bar_d (restriction_diagram f D) n (cycle_inclusion (bar_complex D) n z) = 0).
rewrite bar_scalar_d; exact (submodule_val_mem z).
Defined.

Lemma bar_scalar_cohomology_pi (D : module_codiagram B C) n
    (z : cycle_module (bar_complex D) n) :
  module_hom_fun (iso_hom (bar_scalar_cohomology_iso f D n))
    (quotient_pi (boundaries_in_cycles (bar_complex D) n) z) =
  quotient_pi (boundaries_in_cycles (bar_complex (restriction_diagram f D)) n)
    (bar_scalar_cycle z).
Proof.
pose zA := @cycle_of_cocycle A (restriction_complex f (bar_complex D)) n
  (cycle_inclusion (bar_complex D) n z) (submodule_val_mem z).
have h : module_hom_fun (iso_inv (scalar_cohomology_iso f (bar_complex D) n))
    (quotient_pi (boundaries_in_cycles (bar_complex D) n) z) =
    quotient_pi (boundaries_in_cycles (restriction_complex f (bar_complex D)) n) zA.
  apply (@module_iso_hom_injective A _ _ (scalar_cohomology_iso f (bar_complex D) n)).
  rewrite module_iso_inv_hom_apply scalar_cohomology_iso_pi.
  congr (quotient_pi _ _); apply submodule_val_injective; reflexivity.
change (cohomology_map (term_iso_cochain_map (@bar_scalar_term_commutes A B f C D)) n
  (module_hom_fun (iso_inv (scalar_cohomology_iso f (bar_complex D) n))
    (quotient_pi (boundaries_in_cycles (bar_complex D) n) z)) =
  quotient_pi (boundaries_in_cycles (bar_complex (restriction_diagram f D)) n) (bar_scalar_cycle z)).
rewrite h cohomology_map_pi; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Theorem bar_scalar_cohomology_naturality (D E : module_codiagram B C)
    (u : nat_trans D E) n (q : cohomology (bar_complex D) n) :
  cohomology_map (bar_cochain_map (restriction_map f u)) n
    (module_hom_fun (iso_hom (bar_scalar_cohomology_iso f D n)) q) =
  module_hom_fun (iso_hom (bar_scalar_cohomology_iso f E n))
    (restricted_linear f (cohomology_map (bar_cochain_map u) n) q).
Proof.
have [z <-] := quotient_pi_surjective q.
change (cohomology_map (bar_cochain_map (restriction_map f u)) n
  (module_hom_fun (iso_hom (bar_scalar_cohomology_iso f D n)) (quotient_pi _ z)) =
  module_hom_fun (iso_hom (bar_scalar_cohomology_iso f E n))
    (cohomology_map (bar_cochain_map u) n (quotient_pi _ z))).
rewrite cohomology_map_pi !bar_scalar_cohomology_pi cohomology_map_pi.
congr (quotient_pi _ _); apply submodule_val_injective; reflexivity.
Qed.

End Scalars.
End DiazParkBarScalarNaturality.
