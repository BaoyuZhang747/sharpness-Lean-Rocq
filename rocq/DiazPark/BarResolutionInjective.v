From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  CategoryInjectives ModuleInfrastructure MackeyModuleCarriers ModuleDiagrams ModuleDiagramDescent
  HomologicalComplex HomologicalCohomology BarPaths BarFreeModule BarComplex
  BarResolutionTerms BarResolutionHom BarResolutionDifferential BarResolutionContraction
  BarResolutionComparison.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkCohomology DiazParkBarPaths DiazParkFreeModule
  DiazParkBarComplex DiazParkBarResolutionTerms DiazParkBarResolutionHom
  DiazParkBarResolutionDifferential DiazParkBarResolutionContraction DiazParkBarResolutionComparison.
Local Open Scope ring_scope.

Module DiazParkBarResolutionInjective.
Section InjectiveAcyclicity.
Variable R : pzRingType.
Variable C : category.

Definition resolution_image_subspace n (x : C) :=
  linear_image (@resolution_boundary_fun R C n x :
    {linear resolution_term_obj (C := C) R n.+1 x -> resolution_term_obj (C := C) R n x}).

Lemma resolution_image_stable n (x y : opposite C) (f : hom (opposite C) x y)
    (v : fobj (@resolution_term R C n) x) :
  resolution_image_subspace n x v -> resolution_image_subspace n y
    (module_hom_fun (fmap (@resolution_term R C n) f) v).
Proof.
move=> [u <-].
exists (module_hom_fun (fmap (@resolution_term R C n.+1) f) u).
exact: (congr1 (fun k => module_hom_fun k u) (naturality (@resolution_boundary R C n) f)).
Qed.

Definition resolution_image n : module_codiagram R C :=
  @subdiagram R (opposite C) (@resolution_term R C n)
    (@resolution_image_subspace n) (@resolution_image_stable n).

Definition resolution_image_inclusion n :
    nat_trans (resolution_image n) (@resolution_term R C n) :=
  @subdiagram_inclusion R (opposite C) (@resolution_term R C n)
    (@resolution_image_subspace n) (@resolution_image_stable n).

Definition resolution_image_projection n :
    nat_trans (@resolution_term R C n.+1) (resolution_image n) :=
  @subdiagram_lift R (opposite C) (@resolution_term R C n)
    (@resolution_image_subspace n) (@resolution_image_stable n)
    (@resolution_term R C n.+1) (@resolution_boundary R C n)
    (fun x v => ex_intro _ v (Logic.eq_refl _)).

Lemma resolution_image_projection_surjective n (x : C) (v : fobj (resolution_image n) x) :
  exists u, module_hom_fun (component (resolution_image_projection n) x) u = v.
Proof.
have [u hu] := submodule_val_mem v.
exists u; apply submodule_val_injective; exact: hu.
Qed.

Variable D : module_codiagram R C.

Lemma term_to_cochain_zero n :
  term_to_cochain (diagram_zero (@resolution_term R C n) D) = 0.
Proof. reflexivity. Qed.

Lemma resolution_cocycle_zero n (alpha : nat_trans (@resolution_term R C n) D) :
  bar_d D n (term_to_cochain alpha) = 0 ->
    nat_comp (@resolution_boundary R C n) alpha =
      diagram_zero (@resolution_term R C n.+1) D.
Proof.
move=> ha; apply term_to_cochain_injective.
by rewrite term_cochain_differential term_to_cochain_zero.
Qed.

Theorem injective_resolution_coboundary
    (hD : injective_object (functor_category (opposite C) (module_category R)) D)
    n (alpha : nat_trans (@resolution_term R C n.+1) D)
    (ha : nat_comp (@resolution_boundary R C n.+1) alpha =
      diagram_zero (@resolution_term R C n.+2) D) :
  exists beta : nat_trans (@resolution_term R C n) D,
    nat_comp (@resolution_boundary R C n) beta = alpha.
Proof.
have hk : forall x (u : fobj (@resolution_term R C n.+1) x),
    module_hom_fun (component (resolution_image_projection n) x) u = 0 ->
    module_hom_fun (component alpha x) u = 0.
  move=> x u hu.
  have hd : @resolution_boundary_fun R C n x u = 0 :=
    congr1 (@submodule_val R (resolution_term_obj (C := C) R n x)
      (resolution_image_subspace n x)) hu.
  have [v <-] := resolution_exact_successor hd.
  exact: (congr1 (fun t : nat_trans (@resolution_term R C n.+2) D =>
    module_hom_fun (component t x) v) ha).
pose t := @diagram_descent R (opposite C) (@resolution_term R C n.+1)
  (resolution_image n) D (resolution_image_projection n) alpha
  (@resolution_image_projection_surjective n) hk.
have hm : @monomorphism (functor_category (opposite C) (module_category R))
    (resolution_image n) (@resolution_term R C n) (resolution_image_inclusion n).
  apply pointwise_injective_monomorphism => x.
  exact: subdiagram_inclusion_injective.
have [beta hb] := hD (resolution_image n) (@resolution_term R C n)
  (resolution_image_inclusion n) hm t.
exists beta; apply nat_trans_ext => x; apply module_hom_ext => u.
have hf := @diagram_descent_factor R (opposite C) (@resolution_term R C n.+1)
  (resolution_image n) D (resolution_image_projection n) alpha
  (@resolution_image_projection_surjective n) hk x u.
have he := congr1 (fun s : nat_trans (resolution_image n) D =>
  module_hom_fun (component s x)
    (module_hom_fun (component (resolution_image_projection n) x) u)) hb.
exact: eq_trans he hf.
Qed.

Theorem injective_bar_positive_acyclic
    (hD : injective_object (functor_category (opposite C) (module_category R)) D) :
  positive_acyclic (bar_complex D).
Proof.
move=> n a ha.
have hz : bar_d D n.+1 (term_to_cochain (cochain_to_term a)) = 0.
  rewrite term_cochain_inverse; exact: ha.
have [beta hb] := injective_resolution_coboundary hD (resolution_cocycle_zero hz).
exists (term_to_cochain beta).
rewrite -term_cochain_differential hb term_cochain_inverse; reflexivity.
Qed.

Theorem injective_bar_cohomology_zero
    (hD : injective_object (functor_category (opposite C) (module_category R)) D)
    n (q : cohomology (bar_complex D) n.+1) : q = 0.
Proof. exact: (proj1 (positive_acyclic_cohomology _) (injective_bar_positive_acyclic hD) n q). Qed.

End InjectiveAcyclicity.
End DiazParkBarResolutionInjective.

