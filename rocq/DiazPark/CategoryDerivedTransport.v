(** Lifting an ordinary natural limit comparison through an actual
    exact injective-preserving diagram functor, using constructed resolutions. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryModuleLinear CategoryModuleLimits CategoryModuleLimitFunctor
  CategoryModuleExactness CategoryInjectives ModuleInfrastructure MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps HomologicalModuleIso
  HomologicalDiagramInjectives HomologicalDiagramLimits CategoryInjectiveResolution
  CategoryInjectiveResolutionComparison CategoryEnoughInjectives CategoryResolutionLimitMaps
  CategoryResolutionTransport CategoryResolutionIndependence CategoryDerivedLimits CategoryComplexIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.
Local Opaque chosen_injective_resolution injective_resolution_comparison
  module_quotient linear_preimage linear_kernel linear_image.

Section Transport.
Variable R : pzRingType.
Variables C D : category.
Variable T : functor (functor_category C (module_category R))
  (functor_category D (module_category R)).
Variable Tzero : diagram_functor_preserves_zero T.
Variable e : @isomorphism
  (functor_category (functor_category C (module_category R)) (module_category R))
  (functor_comp T (module_limit_functor R D)) (module_limit_functor R C).

Definition mapped_limit_term_iso (K : @diagram_complex R C) n :
    @isomorphism (module_category R)
      (cochain_term (limit_complex (mapped_diagram_complex Tzero K)) n)
      (cochain_term (limit_complex K) n) := nat_iso_component e (diagram_term K n).

Lemma mapped_limit_term_commutes (K : @diagram_complex R C) n x :
    cochain_d (limit_complex K) n (module_hom_fun (iso_hom (mapped_limit_term_iso K n)) x) =
    module_hom_fun (iso_hom (mapped_limit_term_iso K n.+1))
      (cochain_d (limit_complex (mapped_diagram_complex Tzero K)) n x).
Proof.
symmetry. exact (congr1 (fun h : module_hom
  (module_limit_type (fobj T (diagram_term K n))) (module_limit_type (diagram_term K n.+1)) => h x)
  (naturality (iso_hom e) (diagram_d K n))).
Qed.

Definition mapped_limit_cohomology_iso (K : @diagram_complex R C) n :
    @isomorphism (module_category R)
      [the lmodType R of cohomology (limit_complex (mapped_diagram_complex Tzero K)) n]
      [the lmodType R of cohomology (limit_complex K) n] :=
  term_iso_cohomology_iso (@mapped_limit_term_commutes K) n.

Lemma mapped_limit_cohomology_naturality {K L : @diagram_complex R C}
    (a : diagram_cochain_map K L) n
    (q : cohomology (limit_complex (mapped_diagram_complex Tzero K)) n) :
    module_hom_fun (iso_hom (mapped_limit_cohomology_iso L n))
      (cohomology_map (limit_cochain_map (mapped_diagram_cochain_map Tzero a)) n q) =
    cohomology_map (limit_cochain_map a) n
      (module_hom_fun (iso_hom (mapped_limit_cohomology_iso K n)) q).
Proof.
apply cohomology_map_square. intros k x.
exact (congr1 (fun h : module_hom
  (module_limit_type (fobj T (diagram_term K k))) (module_limit_type (diagram_term L k)) => h x)
  (naturality (iso_hom e) (diagram_cochain_map_at a k))).
Qed.

Variable Texact : diagram_functor_preserves_exact T.
Variable Tmono : diagram_functor_preserves_injections T.
Variable Tinj : forall F,
  injective_object (functor_category C (module_category R)) F ->
  injective_object (functor_category D (module_category R)) (fobj T F).

Definition transported_resolution (F : module_diagram R C) : injective_resolution (fobj T F) :=
  mapped_injective_resolution Tzero Texact Tmono Tinj (chosen_injective_resolution R F).

Definition derived_limit_transport_iso (F : module_diagram R C) n :
    @isomorphism (module_category R) (derived_limit R (fobj T F) n) (derived_limit R F n) :=
  module_iso_comp (derived_limit_resolution_iso (transported_resolution F) n)
    (mapped_limit_cohomology_iso (injective_resolution_complex (chosen_injective_resolution R F)) n).

Theorem derived_limit_transport_naturality {F G : module_diagram R C}
    (u : nat_trans F G) n :
    module_hom_comp (derived_limit_map R (fmap T u) n) (iso_hom (derived_limit_transport_iso G n)) =
      module_hom_comp (iso_hom (derived_limit_transport_iso F n)) (derived_limit_map R u n).
Proof.
pose (a := injective_resolution_comparison (chosen_injective_resolution R F) (chosen_injective_resolution R G) u).
pose (b := mapped_injective_resolution_map Tzero Texact Tmono Tinj a).
pose (c := injective_resolution_comparison (chosen_injective_resolution R (fobj T F))
  (chosen_injective_resolution R (fobj T G)) (fmap T u)).
have h := resolution_cohomology_iso_naturality c b n.
apply module_hom_ext; intro q.
have hq := congr1 (fun f : module_hom (derived_limit R (fobj T F) n)
  (resolution_cohomology (transported_resolution G) n) => f q) h.
change (module_hom_fun (iso_hom (mapped_limit_cohomology_iso
  (injective_resolution_complex (chosen_injective_resolution R G)) n))
  (module_hom_fun (iso_hom (derived_limit_resolution_iso (transported_resolution G) n))
    (module_hom_fun (resolution_cohomology_map c n) q)) =
  module_hom_fun (resolution_cohomology_map a n)
    (module_hom_fun (iso_hom (mapped_limit_cohomology_iso
      (injective_resolution_complex (chosen_injective_resolution R F)) n))
      (module_hom_fun (iso_hom (derived_limit_resolution_iso (transported_resolution F) n)) q))).
change (module_hom_fun (iso_hom (derived_limit_resolution_iso (transported_resolution G) n))
  (module_hom_fun (resolution_cohomology_map c n) q) =
  module_hom_fun (resolution_cohomology_map b n)
    (module_hom_fun (iso_hom (derived_limit_resolution_iso (transported_resolution F) n)) q)) in hq.
rewrite hq. exact: mapped_limit_cohomology_naturality.
Qed.

Definition derived_limit_transport_nat_iso (n : nat) : @isomorphism
    (functor_category (functor_category C (module_category R)) (module_category R))
    (functor_comp T (derived_limit_functor R D n)) (derived_limit_functor R C n) :=
  @nat_iso_of_components (functor_category C (module_category R)) (module_category R)
    (functor_comp T (derived_limit_functor R D n)) (derived_limit_functor R C n)
    (fun F => derived_limit_transport_iso F n)
    (fun F G u => derived_limit_transport_naturality u n).
End Transport.


