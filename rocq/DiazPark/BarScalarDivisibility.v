From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps MackeyStructures
  MackeySubquotients MackeyScalarSubquotients MackeyBarReduction
  HomologicalComplex HomologicalCohomology HomologicalCohomologyMaps
  HomologicalShortExactMaps HomologicalModuleIso BarComplex BarNaturality BarExactness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkCohomologyMaps
  DiazParkHomologicalModuleIso DiazParkBarComplex DiazParkBarNaturality DiazParkBarExactness.
Local Open Scope ring_scope.

(** The two genuine scalar exact sequences of Mackey coefficients.  The
    conclusions use only positive-degree vanishing of kernel and cokernel. *)
Section ScalarDivisibility.
Variable R : comPzRingType.
Variables C D : category.
Variable B : mackey_shape C.
Variable L : functor D C.
Variable M : mackey_module R B.
Variable r : R.

Definition mackey_scalar_to_image :
  mackey_hom M (subfunctor_mackey (mackey_scalar_image M r)).
Proof.
refine (@MackeyHom R C B M (subfunctor_mackey (mackey_scalar_image M r))
  (fun P => @scalar_to_image R (mackey_value M P) r) _ _).
- move=> P Q f x; apply submodule_val_injective.
  change (r *: mackey_pull M f x = mackey_pull M f (r *: x)).
  by rewrite linearZ.
- move=> P Q f x; apply submodule_val_injective.
  change (r *: mackey_push M f x = mackey_push M f (r *: x)).
  by rewrite linearZ.
Defined.

Let K := subfunctor_mackey (mackey_scalar_kernel M r).
Let I := subfunctor_mackey (mackey_scalar_image M r).
Let Q := quotient_mackey (mackey_scalar_image M r).
Let KM := mackey_codiagram_map L (subfunctor_inclusion (mackey_scalar_kernel M r)).
Let MI := mackey_codiagram_map L mackey_scalar_to_image.
Let IM := mackey_codiagram_map L (subfunctor_inclusion (mackey_scalar_image M r)).
Let MQ := mackey_codiagram_map L (quotient_projection (mackey_scalar_image M r)).

Definition scalar_kernel_bar_short_exact :
  degreewise_short_exact (bar_cochain_map KM) (bar_cochain_map MI).
Proof.
apply: bar_short_exact.
- move=> P; exact: submodule_val_injective.
- move=> P x.
  change (@scalar_to_image R (mackey_value M (fobj L P)) r (submodule_val x) = 0).
  apply/(scalar_to_image_zero r).
  exact: (submodule_val_mem x).
- move=> P x hx.
  have h : @scalar_kernel R (mackey_value M (fobj L P)) r x.
    apply/(scalar_to_image_zero r); exact: hx.
  exists (@submodule_in R (mackey_value M (fobj L P))
    (@scalar_kernel R (mackey_value M (fobj L P)) r) x h).
  reflexivity.
- move=> P x; exact: scalar_to_image_surjective.
Defined.

Definition scalar_image_bar_short_exact :
  degreewise_short_exact (bar_cochain_map IM) (bar_cochain_map MQ).
Proof.
apply: bar_short_exact.
- move=> P; exact: submodule_val_injective.
- move=> P x; apply/quotient_pi_kernel; exact: submodule_val_mem.
- move=> P x hx.
  have h : @scalar_image R (mackey_value M (fobj L P)) r x
    by apply/quotient_pi_kernel; exact: hx.
  exists (@submodule_in R (mackey_value M (fobj L P))
    (@scalar_image R (mackey_value M (fobj L P)) r) x h).
  reflexivity.
- move=> P x; exact: quotient_pi_surjective.
Defined.

Lemma scalar_cohomology_factor n (q : cohomology (bar_complex (mackey_codiagram L M)) n) :
  cohomology_map (bar_cochain_map IM) n
    (cohomology_map (bar_cochain_map MI) n q) = r *: q.
Proof.
have [z <-] := quotient_pi_surjective q.
rewrite !cohomology_map_pi -linearZ.
congr (quotient_pi _ _); apply submodule_val_injective.
apply functional_extensionality_dep => P.
apply functional_extensionality_dep => p; reflexivity.
Qed.

Definition scalar_image_cohomology_iso
    (hK : mackey_bar_acyclic L K) n :
  @isomorphism (module_category R)
    (cohomology (bar_complex (mackey_codiagram L M)) n.+1)
    (cohomology (bar_complex (mackey_codiagram L I)) n.+1) :=
  cohomology_quotient_iso scalar_kernel_bar_short_exact
    (proj1 (positive_acyclic_cohomology _) hK n)
    (proj1 (positive_acyclic_cohomology _) hK n.+1).

Lemma scalar_image_cohomology_iso_hom
    (hK : mackey_bar_acyclic L K) n q :
  module_hom_fun (iso_hom (scalar_image_cohomology_iso hK n)) q =
    cohomology_map (bar_cochain_map MI) n.+1 q.
Proof. reflexivity. Qed.

Theorem mackey_scalar_cohomology_surjective
    (hK : mackey_bar_acyclic L K) (hQ : mackey_bar_acyclic L Q) n :
  forall q : cohomology (bar_complex (mackey_codiagram L M)) n.+1,
    exists y, r *: y = q.
Proof.
move=> q.
have [a ha] := cohomology_inclusion_surjective scalar_image_bar_short_exact
  (proj1 (positive_acyclic_cohomology _) hQ n) q.
have [y hy] := cohomology_quotient_surjective scalar_kernel_bar_short_exact
  (proj1 (positive_acyclic_cohomology _) hK n.+1) a.
exists y; rewrite -(scalar_cohomology_factor y) hy; exact: ha.
Qed.

End ScalarDivisibility.
