From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleProducts
  CategoryModuleLimits ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient ModuleDiagrams
  HomologicalComplex HomologicalCohomology HomologicalDiagramInjectives HomologicalDiagramLimits
  HomologicalModuleIso CategoryInjectiveResolution BarComplex BarResolutionInjective
  BarInjectiveResolutionTail BarConnectingLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalModuleIso
  DiazParkBarComplex DiazParkBarResolutionInjective DiazParkBarInjectiveResolutionTail
  DiazParkBarConnectingLimit.
Local Open Scope ring_scope.

Module DiazParkBarInjectiveDegreeOne.
Section One.
Variable R : pzRingType.
Variable C : category.
Variable D : module_codiagram R C.
Variable J : injective_resolution D.
Let K := injective_resolution_complex J.
Let L := limit_complex K.
Let Z := injective_syzygy J.

Lemma first_cycle_coordinate_zero (z : cycle_module L 1) (x : opposite C) :
  module_hom_fun (component (diagram_d K 1) x)
    (module_limit_val (cycle_inclusion L 1 z) x) = 0.
Proof.
have h := congr1 (fun v : module_limit_type (diagram_term K 2) => module_limit_val v x)
  (submodule_val_mem z).
change (module_limit_val (limit_action (diagram_d K 1) (cycle_inclusion L 1 z)) x = 0) in h.
rewrite limit_action_coordinate in h; exact: h.
Qed.

Definition first_cycle_limit_fun (z : cycle_module L 1) : module_limit_type Z.
Proof.
refine (@submodule_in R (module_product_type (fobj Z)) (module_limit_subspace Z)
  (fun x => @submodule_in R (fobj (diagram_term K 1) x)
    (diagram_kernel_subspace (diagram_d K 1) x)
    (module_limit_val (cycle_inclusion L 1 z) x) (first_cycle_coordinate_zero z x)) _).
move=> x y f; apply submodule_val_injective.
exact: (module_limit_val_compatible (cycle_inclusion L 1 z) f).
Defined.

Definition first_cycle_limit :
    module_hom [the lmodType R of cycle_module L 1] (module_limit_type Z).
Proof.
exists first_cycle_limit_fun; move=> r a b.
apply module_limit_val_injective; apply functional_extensionality_dep => x.
apply submodule_val_injective; reflexivity.
Defined.

Lemma first_cycle_limit_coordinate (z : cycle_module L 1) x :
  submodule_val (module_limit_val (first_cycle_limit z) x) =
    module_limit_val (cycle_inclusion L 1 z) x.
Proof. reflexivity. Qed.

Definition first_limit_cycle_fun (v : module_limit_type Z) : cycle_module L 1.
Proof.
refine (@cycle_of_cocycle R L 1
  (limit_action (diagram_cycle_inclusion K 1) v) _).
apply module_limit_val_injective; apply functional_extensionality_dep => x.
change (module_limit_val (limit_action (diagram_d K 1)
  (limit_action (diagram_cycle_inclusion K 1) v)) x = 0).
rewrite !limit_action_coordinate.
exact: (submodule_val_mem (module_limit_val v x)).
Defined.

Definition first_limit_cycle :
    module_hom (module_limit_type Z) [the lmodType R of cycle_module L 1].
Proof.
exists first_limit_cycle_fun; move=> r a b.
apply submodule_val_injective.
change (limit_action (diagram_cycle_inclusion K 1) (r *: a + b) =
  r *: limit_action (diagram_cycle_inclusion K 1) a + limit_action (diagram_cycle_inclusion K 1) b).
exact: linearP.
Defined.

Lemma first_limit_cycle_inverse (z : cycle_module L 1) :
  first_limit_cycle (first_cycle_limit z) = z.
Proof.
apply submodule_val_injective; apply module_limit_val_injective.
apply functional_extensionality_dep => x.
change (module_limit_val (limit_action (diagram_cycle_inclusion K 1) (first_cycle_limit z)) x =
  module_limit_val (cycle_inclusion L 1 z) x).
rewrite limit_action_coordinate; reflexivity.
Qed.

Lemma first_cycle_limit_inverse (v : module_limit_type Z) :
  first_cycle_limit (first_limit_cycle v) = v.
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep => x.
apply submodule_val_injective.
change (module_limit_val (limit_action (diagram_cycle_inclusion K 1) v) x =
  submodule_val (module_limit_val v x)).
rewrite limit_action_coordinate; reflexivity.
Qed.

Lemma first_cycle_boundary_equation (w : module_limit_type (diagram_term K 0))
    (z : cycle_module L 1) :
  limit_action (injective_syzygy_map J) w = first_cycle_limit z <->
    limit_action (diagram_d K 0) w = cycle_inclusion L 1 z.
Proof.
split.
- move=> h; apply module_limit_val_injective; apply functional_extensionality_dep => x.
  have he := congr1 (fun v : module_limit_type Z => submodule_val (module_limit_val v x)) h.
  rewrite limit_action_coordinate first_cycle_limit_coordinate in he.
  rewrite limit_action_coordinate; exact: he.
- move=> h; apply module_limit_val_injective; apply functional_extensionality_dep => x.
  apply submodule_val_injective.
  rewrite limit_action_coordinate first_cycle_limit_coordinate.
  have he := congr1 (fun v : module_limit_type (diagram_term K 1) => module_limit_val v x) h.
  rewrite limit_action_coordinate in he; exact: he.
Qed.

Lemma first_cycle_boundaries (z : cycle_module L 1) :
  boundaries_in_cycles L 1 z <->
    exists w : module_limit_type (diagram_term K 0),
      limit_action (injective_syzygy_map J) w = first_cycle_limit z.
Proof.
change ((exists w, limit_action (diagram_d K 0) w = cycle_inclusion L 1 z) <->
  exists w : module_limit_type (diagram_term K 0), limit_action (injective_syzygy_map J) w = first_cycle_limit z).
split; move=> [w hw]; exists w.
- exact: (proj2 (first_cycle_boundary_equation w z) hw).
- exact: (proj1 (first_cycle_boundary_equation w z) hw).
Qed.

Definition first_cycle_connecting : {linear cycle_module L 1 -> cohomology (bar_complex D) 1} :=
  (limit_connecting (injective_syzygy_bar_short_exact J) \o module_hom_to_linear first_cycle_limit :
    {linear cycle_module L 1 -> cohomology (bar_complex D) 1}).

Lemma first_cycle_connecting_kernel (z : cycle_module L 1) :
  boundaries_in_cycles L 1 z <-> first_cycle_connecting z = 0.
Proof.
change (boundaries_in_cycles L 1 z <->
  limit_connecting (injective_syzygy_bar_short_exact J) (first_cycle_limit z) = 0).
rewrite limit_connecting_kernel; exact: first_cycle_boundaries.
Qed.

Lemma first_cycle_connecting_surjective :
  forall q : cohomology (bar_complex D) 1, exists z, first_cycle_connecting z = q.
Proof.
move=> q.
have hI := injective_bar_positive_acyclic (injective_resolution_term_injective J 0).
have [v hv] := limit_connecting_surjective (injective_syzygy_bar_short_exact J) hI q.
exists (first_limit_cycle v).
change (limit_connecting (injective_syzygy_bar_short_exact J)
  (first_cycle_limit (first_limit_cycle v)) = q).
by rewrite first_cycle_limit_inverse.
Qed.

Local Opaque module_quotient linear_preimage linear_kernel linear_image.
Definition bar_injective_degree_one_iso : @isomorphism (module_category R)
    [the lmodType R of cohomology (bar_complex D) 1]
    [the lmodType R of cohomology L 1] :=
  iso_symm (@quotient_linear_iso R (cycle_module L 1)
    [the lmodType R of cohomology (bar_complex D) 1] (boundaries_in_cycles L 1)
    first_cycle_connecting first_cycle_connecting_kernel first_cycle_connecting_surjective).

End One.
End DiazParkBarInjectiveDegreeOne.

