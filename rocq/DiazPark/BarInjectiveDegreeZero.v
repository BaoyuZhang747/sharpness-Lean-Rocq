(** The augmentation identifies the ordinary limit with degree-zero
    cohomology of the actual limit of an augmented injective resolution.
    Only augmentation injectivity and exactness at degree zero are used. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  CategoryModuleProducts CategoryModuleLimits ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient HomologicalComplex
  HomologicalCohomology HomologicalDiagramInjectives HomologicalDiagramLimits
  HomologicalModuleIso CategoryInjectiveResolution.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology
  DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DiazParkBarInjectiveDegreeZero.
Section Zero.
Variable R : pzRingType.
Variable C : category.
Variable D : module_diagram R C.
Variable J : injective_resolution D.
Let K := injective_resolution_complex J.
Let L := limit_complex K.
Let a := injective_resolution_augmentation J.

Lemma zero_cycle_coordinate_zero (z : cycle_module L 0) x :
    module_hom_fun (component (diagram_d K 0) x)
      (module_limit_val (cycle_inclusion L 0 z) x) = 0.
Proof.
have h := congr1 (fun v : module_limit_type (diagram_term K 1) => module_limit_val v x)
  (submodule_val_mem z).
change (module_limit_val (limit_action (diagram_d K 0) (cycle_inclusion L 0 z)) x = 0) in h.
rewrite limit_action_coordinate in h; exact: h.
Qed.

Lemma zero_cycle_coordinate_preimage (z : cycle_module L 0) x :
    exists v, module_hom_fun (component a x) v = module_limit_val (cycle_inclusion L 0 z) x.
Proof.
apply/(injective_resolution_exact_zero J x _).
exact: zero_cycle_coordinate_zero.
Qed.

Definition zero_cycle_preimage (z : cycle_module L 0) x : fobj D x :=
  proj1_sig (constructive_indefinite_description (zero_cycle_coordinate_preimage z x)).

Lemma zero_cycle_preimage_spec (z : cycle_module L 0) x :
    module_hom_fun (component a x) (zero_cycle_preimage z x) =
      module_limit_val (cycle_inclusion L 0 z) x.
Proof. exact: (proj2_sig (constructive_indefinite_description (zero_cycle_coordinate_preimage z x))). Qed.

Lemma zero_cycle_preimage_compatible (z : cycle_module L 0) x y (f : hom C x y) :
    module_hom_fun (fmap D f) (zero_cycle_preimage z x) = zero_cycle_preimage z y.
Proof.
apply (injective_resolution_augmentation_injective J y).
have h := congr1 (fun g : module_hom (fobj D x) (fobj (diagram_term K 0) y) =>
  module_hom_fun g (zero_cycle_preimage z x)) (naturality a f).
change (module_hom_fun (component a y) (module_hom_fun (fmap D f) (zero_cycle_preimage z x)) =
  module_hom_fun (fmap (diagram_term K 0) f) (module_hom_fun (component a x) (zero_cycle_preimage z x))) in h.
rewrite h !zero_cycle_preimage_spec.
exact: (module_limit_val_compatible (cycle_inclusion L 0 z) f).
Qed.

Definition zero_cycle_limit_fun (z : cycle_module L 0) : module_limit_type D :=
  @submodule_in R (module_product_type (fobj D)) (module_limit_subspace D)
    (zero_cycle_preimage z) (zero_cycle_preimage_compatible z).

Definition zero_cycle_limit :
    module_hom [the lmodType R of cycle_module L 0] (module_limit_type D).
Proof.
exists zero_cycle_limit_fun; move=> r z w.
apply module_limit_val_injective; apply functional_extensionality_dep => x.
change (zero_cycle_preimage (r *: z + w) x = r *: zero_cycle_preimage z x + zero_cycle_preimage w x).
apply (injective_resolution_augmentation_injective J x).
rewrite module_hom_linear !zero_cycle_preimage_spec.
rewrite linearP module_limit_val_linear. reflexivity.
Defined.

Definition zero_limit_cycle_fun (v : module_limit_type D) : cycle_module L 0.
Proof.
refine (@cycle_of_cocycle R L 0 (limit_action a v) _).
apply module_limit_val_injective; apply functional_extensionality_dep => x.
change (module_limit_val (limit_action (diagram_d K 0) (limit_action a v)) x = 0).
rewrite !limit_action_coordinate.
exact: injective_resolution_augmentation_zero.
Defined.

Definition zero_limit_cycle :
    module_hom (module_limit_type D) [the lmodType R of cycle_module L 0].
Proof.
exists zero_limit_cycle_fun; move=> r v w.
apply submodule_val_injective.
change (limit_action a (r *: v + w) = r *: limit_action a v + limit_action a w).
exact: linearP.
Defined.

Lemma zero_cycle_limit_inverse (v : module_limit_type D) :
    zero_cycle_limit (zero_limit_cycle v) = v.
Proof.
apply module_limit_val_injective; apply functional_extensionality_dep => x.
apply (injective_resolution_augmentation_injective J x).
change (module_hom_fun (component a x) (zero_cycle_preimage (zero_limit_cycle v) x) =
  module_hom_fun (component a x) (module_limit_val v x)).
rewrite zero_cycle_preimage_spec.
exact: limit_action_coordinate.
Qed.

Lemma zero_limit_cycle_inverse (z : cycle_module L 0) :
    zero_limit_cycle (zero_cycle_limit z) = z.
Proof.
apply submodule_val_injective; apply module_limit_val_injective.
apply functional_extensionality_dep => x.
change (module_limit_val (limit_action a (zero_cycle_limit z)) x =
  module_limit_val (cycle_inclusion L 0 z) x).
rewrite limit_action_coordinate. exact: zero_cycle_preimage_spec.
Qed.

Lemma zero_cycle_limit_kernel (z : cycle_module L 0) :
    boundaries_in_cycles L 0 z <-> zero_cycle_limit z = 0.
Proof.
change (cycle_inclusion L 0 z = 0 <-> zero_cycle_limit z = 0).
split.
- move=> hz.
  have hz0 : z = 0 by apply submodule_val_injective; exact hz.
  rewrite hz0. exact: module_hom_zero.
- move=> hz.
  have hz0 : z = 0.
    rewrite -(zero_limit_cycle_inverse z) hz. exact: module_hom_zero.
  rewrite hz0. exact: linear0.
Qed.

Lemma zero_cycle_limit_surjective (v : module_limit_type D) :
    exists z, zero_cycle_limit z = v.
Proof. exists (zero_limit_cycle v); exact: zero_cycle_limit_inverse. Qed.

Local Opaque module_quotient linear_preimage linear_kernel linear_image.
Definition injective_degree_zero_iso : @isomorphism (module_category R)
    (module_limit_type D) [the lmodType R of cohomology L 0] :=
  iso_symm (@quotient_linear_iso R [the lmodType R of cycle_module L 0]
    (module_limit_type D) (boundaries_in_cycles L 0)
    (module_hom_to_linear zero_cycle_limit) zero_cycle_limit_kernel zero_cycle_limit_surjective).

End Zero.
End DiazParkBarInjectiveDegreeZero.
