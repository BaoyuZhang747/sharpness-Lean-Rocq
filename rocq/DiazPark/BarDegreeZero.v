From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleProducts
  CategoryModuleLimits ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  HomologicalComplex HomologicalCohomology HomologicalDegreeZero
  BarPaths BarCofaces BarComplex BarResolutionComparison.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkHomologicalDegreeZero
  DiazParkBarPaths DiazParkBarCofaces DiazParkBarComplex DiazParkBarResolutionComparison.
Local Open Scope ring_scope.

Module DiazParkBarDegreeZero.
Section Zero.
Variable R : pzRingType.
Variable C : category.
Variable D : module_codiagram R C.

Lemma bar_zero_d_formula (a : bar_term D 0) (x y : C) (f : hom C x y) :
  bar_d D 0 a x (existT _ y (f, tt)) =
    module_hom_fun (fmap D f) (a y tt) - a x tt.
Proof.
change (@bar_evaluation R C D 1 x (existT _ y (f, tt)) (bar_d D 0 a) = module_hom_fun (fmap D f) (a y tt) - a x tt).
rewrite bar_d_formula linear_sum !big_ord_recl big_ord0 !linearZ expr0 expr1.
change (1 *: module_hom_fun (fmap D f) (a y tt) + ((-1) *: a x tt + 0) =
  module_hom_fun (fmap D f) (a y tt) - a x tt).
by rewrite scale1r scaleN1r addr0.
Qed.

Lemma bar_zero_cocycle_compatible (a : bar_term D 0) :
  cocycle (bar_complex D) 0 a <->
  forall (x y : C) (f : hom C x y), module_hom_fun (fmap D f) (a y tt) = a x tt.
Proof.
split.
- move=> ha x y f.
  have h := congr1 (fun b : bar_term D 1 => b x (existT _ y (f, tt))) ha.
  change (bar_d D 0 a x (existT _ y (f, tt)) = 0) in h.
  rewrite bar_zero_d_formula in h; exact: subr0_eq h.
- move=> ha; apply functional_extensionality_dep => x.
  apply functional_extensionality_dep => p; case: p => y [f []].
  change (bar_d D 0 a x (existT _ y (f, tt)) = 0).
  by rewrite bar_zero_d_formula ha subrr.
Qed.

Definition bar_cycle_to_limit_fun (z : cycle_module (bar_complex D) 0) : module_limit_type D.
Proof.
refine (@submodule_in R (module_product_type (fobj D)) (module_limit_subspace D)
  (fun x => submodule_val z x tt) _).
move=> x y f.
exact: (proj1 (bar_zero_cocycle_compatible (submodule_val z)) (submodule_val_mem z) y x f).
Defined.

Definition bar_cycle_to_limit :
    module_hom [the lmodType R of cycle_module (bar_complex D) 0] (module_limit_type D).
Proof.
exists bar_cycle_to_limit_fun; move=> r a b.
apply module_limit_val_injective; apply functional_extensionality_dep => x.
reflexivity.
Defined.

Definition bar_limit_to_cycle_fun (v : module_limit_type D) : cycle_module (bar_complex D) 0.
Proof.
refine (@cycle_of_cocycle R (bar_complex D) 0
  (fun x _ => module_limit_val v x) _).
apply/bar_zero_cocycle_compatible => x y f.
exact: (module_limit_val_compatible v f).
Defined.

Definition bar_limit_to_cycle :
    module_hom (module_limit_type D) [the lmodType R of cycle_module (bar_complex D) 0].
Proof.
exists bar_limit_to_cycle_fun; move=> r a b.
apply submodule_val_injective; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p; reflexivity.
Defined.

Lemma bar_limit_cycle_inverse (z : cycle_module (bar_complex D) 0) :
  bar_limit_to_cycle (bar_cycle_to_limit z) = z.
Proof.
apply submodule_val_injective; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p; by case: p.
Qed.

Lemma bar_cycle_limit_inverse (v : module_limit_type D) :
  bar_cycle_to_limit (bar_limit_to_cycle v) = v.
Proof. apply module_limit_val_injective; reflexivity. Qed.

Definition bar_zero_cohomology_limit_iso :
    @isomorphism (module_category R)
      [the lmodType R of cohomology (bar_complex D) 0] (module_limit_type D).
Proof.
refine (@Build_isomorphism (module_category R) _ _
  (module_hom_comp (module_hom_of_linear (cohomology_zero_cycle (bar_complex D))) bar_cycle_to_limit)
  (module_hom_comp bar_limit_to_cycle
    (module_hom_of_linear (quotient_pi (boundaries_in_cycles (bar_complex D) 0) :
      {linear cycle_module (bar_complex D) 0 -> cohomology (bar_complex D) 0}))) _ _).
- apply module_hom_ext => z.
  change (quotient_pi (boundaries_in_cycles (bar_complex D) 0)
    (bar_limit_to_cycle (bar_cycle_to_limit (cohomology_zero_cycle (bar_complex D) z))) = z).
  rewrite bar_limit_cycle_inverse; exact: cohomology_zero_pi_cycle.
- apply module_hom_ext => z.
  change (bar_cycle_to_limit (cohomology_zero_cycle (bar_complex D)
    (quotient_pi (boundaries_in_cycles (bar_complex D) 0) (bar_limit_to_cycle z))) = z).
  rewrite cohomology_zero_cycle_pi; exact: bar_cycle_limit_inverse.
Defined.

End Zero.
End DiazParkBarDegreeZero.

