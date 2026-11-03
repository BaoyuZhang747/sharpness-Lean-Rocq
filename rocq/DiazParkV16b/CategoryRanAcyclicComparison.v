(** All-degree native higher-limit comparison for the actual right Kan
    extension of one coefficient diagram with positive comma acyclicity. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleExactness CategoryModuleRightKan CategoryModuleRightKanLimits
  CategoryInjectiveResolution CategoryInjectiveResolutionComparison
  CategoryEnoughInjectives CategoryResolutionTransport CategoryResolutionIndependence
  CategoryDerivedLimits CategoryDerivedTransport CategoryRanResolution
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalModuleIso CategoryResolutionLimitMaps CategoryComplexIso
  ModuleInfrastructure MackeyModuleQuotient HomologicalDiagramInjectives.
From DiazParkV16b Require Import CategoryRanAcyclicComparisonResolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.
Local Opaque chosen_injective_resolution injective_resolution_comparison
  module_quotient linear_preimage linear_kernel linear_image.

Section AcyclicComparison.
Variable R : pzRingType.
Variables C D : category.
Variable r : functor C D.

Definition ran_acyclic_resolution_map {F G : module_diagram R C}
    {X : injective_resolution F} {Y : injective_resolution G}
    (hF : ran_comma_positive_acyclic R r F)
    (hG : ran_comma_positive_acyclic R r G)
    {u : nat_trans F G} (a : injective_resolution_map X Y u) :
    injective_resolution_map
      (ran_acyclic_injective_resolution R r X hF)
      (ran_acyclic_injective_resolution R r Y hG)
      (fmap (module_ran R r) u).
Proof.
refine (@Build_injective_resolution_map R D
  (fobj (module_ran R r) F) (fobj (module_ran R r) G)
  (ran_acyclic_injective_resolution R r X hF)
  (ran_acyclic_injective_resolution R r Y hG)
  (fmap (module_ran R r) u)
  (mapped_diagram_cochain_map (@module_ran_preserves_zero R C D r)
    (resolution_map_complex a)) _).
have h := congr1 (@fmap _ _ (module_ran R r) _ _) (resolution_map_augmentation a).
rewrite !fmap_compose in h; exact h.
Defined.

Definition ran_acyclic_higher_limit_iso (F : module_diagram R C)
    (hF : ran_comma_positive_acyclic R r F) n :
    @isomorphism (module_category R)
      (derived_limit R (fobj (module_ran R r) F) n) (derived_limit R F n) :=
  module_iso_comp
    (derived_limit_resolution_iso
      (ran_acyclic_injective_resolution R r (chosen_injective_resolution R F) hF) n)
    (@mapped_limit_cohomology_iso R C D (module_ran R r)
      (@module_ran_preserves_zero R C D r) (module_ran_limit_nat_iso R r)
      (injective_resolution_complex (chosen_injective_resolution R F)) n).

Theorem ran_acyclic_higher_limit_naturality
    {F G : module_diagram R C}
    (hF : ran_comma_positive_acyclic R r F)
    (hG : ran_comma_positive_acyclic R r G)
    (u : nat_trans F G) n :
    module_hom_comp (derived_limit_map R (fmap (module_ran R r) u) n)
      (iso_hom (ran_acyclic_higher_limit_iso hG n)) =
    module_hom_comp (iso_hom (ran_acyclic_higher_limit_iso hF n))
      (derived_limit_map R u n).
Proof.
pose (a := injective_resolution_comparison
  (chosen_injective_resolution R F) (chosen_injective_resolution R G) u).
pose (b := ran_acyclic_resolution_map hF hG a).
pose (c := injective_resolution_comparison
  (chosen_injective_resolution R (fobj (module_ran R r) F))
  (chosen_injective_resolution R (fobj (module_ran R r) G)) (fmap (module_ran R r) u)).
have h := resolution_cohomology_iso_naturality c b n.
apply module_hom_ext; intro q.
have hq := congr1 (fun f : module_hom (derived_limit R (fobj (module_ran R r) F) n)
  (resolution_cohomology
    (ran_acyclic_injective_resolution R r (chosen_injective_resolution R G) hG) n) => f q) h.
change (module_hom_fun (iso_hom (@mapped_limit_cohomology_iso R C D (module_ran R r)
  (@module_ran_preserves_zero R C D r) (module_ran_limit_nat_iso R r)
  (injective_resolution_complex (chosen_injective_resolution R G)) n))
  (module_hom_fun (iso_hom (derived_limit_resolution_iso
    (ran_acyclic_injective_resolution R r (chosen_injective_resolution R G) hG) n))
    (module_hom_fun (resolution_cohomology_map c n) q)) =
  module_hom_fun (resolution_cohomology_map a n)
    (module_hom_fun (iso_hom (@mapped_limit_cohomology_iso R C D (module_ran R r)
      (@module_ran_preserves_zero R C D r) (module_ran_limit_nat_iso R r)
      (injective_resolution_complex (chosen_injective_resolution R F)) n))
      (module_hom_fun (iso_hom (derived_limit_resolution_iso
        (ran_acyclic_injective_resolution R r (chosen_injective_resolution R F) hF) n)) q))).
change (module_hom_fun (iso_hom (derived_limit_resolution_iso
    (ran_acyclic_injective_resolution R r (chosen_injective_resolution R G) hG) n))
  (module_hom_fun (resolution_cohomology_map c n) q) =
  module_hom_fun (resolution_cohomology_map b n)
    (module_hom_fun (iso_hom (derived_limit_resolution_iso
      (ran_acyclic_injective_resolution R r (chosen_injective_resolution R F) hF) n)) q)) in hq.
rewrite hq.
exact: mapped_limit_cohomology_naturality.
Qed.
End AcyclicComparison.

Arguments ran_acyclic_higher_limit_iso R {C D} r {F} hF n.
Arguments ran_acyclic_higher_limit_naturality R {C D} r {F G} hF hG u n.
