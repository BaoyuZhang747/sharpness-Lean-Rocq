(** Native cohomology commutes with arbitrary products of module complexes.
    Representatives and boundary primitives are chosen pointwise using the
    already audited classical-choice foundation; no finite index set occurs. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleProducts
  HomologicalComplex HomologicalMaps HomologicalCohomology HomologicalCohomologyMaps
  HomologicalModuleIso ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkHomologicalMaps DiazParkCohomology
  DiazParkCohomologyMaps DiazParkHomologicalModuleIso.
Local Open Scope ring_scope.

Module DPCochainProduct.
Section Product.
Variable R : pzRingType.
Variable I : Type.
Variable K : I -> cochain_complex R.

Definition product_term n : lmodType R := module_product_type (fun i => cochain_term (K i) n).
Definition product_d n (a : product_term n) : product_term n.+1 := fun i => cochain_d (K i) n (a i).

Lemma product_d_linear n : linear (@product_d n).
Proof. intros r a b; apply functional_extensionality_dep; intro i; exact: linearP. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (product_term n) (product_term n.+1)
  _ (@product_d n) (@product_d_linear n).

Lemma product_d_squared n (a : product_term n) : product_d (product_d a) = 0.
Proof. apply functional_extensionality_dep; intro i; exact: cochain_d2. Qed.

Definition product_complex : cochain_complex R :=
  @CochainComplex R product_term (fun n => (@product_d n : {linear _ -> _})) product_d_squared.

Definition product_projection (i : I) : cochain_map product_complex (K i) :=
  @CochainMap R product_complex (K i)
    (fun n => module_hom_to_linear (module_product_projection (fun i => cochain_term (K i) n) i))
    (fun n a => Logic.eq_refl).

Definition product_cohomology_term n : lmodType R :=
  module_product_type (fun i => [the lmodType R of cohomology (K i) n]).

Definition product_cohomology_at n (a : cohomology product_complex n) : product_cohomology_term n :=
  fun i => cohomology_map (product_projection i) n a.

Lemma product_cohomology_linear n : linear (@product_cohomology_at n).
Proof. intros r a b; apply functional_extensionality_dep; intro i; exact: linearP. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (cohomology product_complex n) (product_cohomology_term n)
  _ (@product_cohomology_at n) (@product_cohomology_linear n).

Lemma product_cohomology_kernel_zero n (a : cohomology product_complex n) :
    product_cohomology_at a = 0 -> a = 0.
Proof.
intro ha; have [z hz] := quotient_pi_surjective a.
have hb : forall i, coboundary (K i) n (cycle_inclusion product_complex n z i).
  intro i.
  have hi := f_equal (fun b : product_cohomology_term n => b i) ha.
  change (cohomology_map (product_projection i) n a = 0) in hi.
  rewrite <- hz in hi; rewrite cohomology_map_pi in hi.
  apply/boundary_subspaceE.
  exact (proj1 (quotient_pi_kernel (boundaries_in_cycles (K i) n)
    (cycle_map (product_projection i) n z)) hi).
rewrite <- hz; apply/quotient_pi_kernel; apply/boundary_subspaceE.
destruct n as [|n].
- apply functional_extensionality_dep; exact hb.
- pose primitive i := proj1_sig (constructive_indefinite_description (hb i)).
  exists primitive; apply functional_extensionality_dep; intro i.
  exact (proj2_sig (constructive_indefinite_description (hb i))).
Qed.

Lemma product_cohomology_injective n : injective (@product_cohomology_at n).
Proof.
intros a b h; have hz : product_cohomology_at (a - b) = 0.
  rewrite linearB.
  change (product_cohomology_at a - product_cohomology_at b = 0).
  by rewrite h subrr.
exact (subr0_eq (product_cohomology_kernel_zero hz)).
Qed.

Lemma product_cohomology_surjective n :
    forall a : product_cohomology_term n, exists b, product_cohomology_at b = a.
Proof.
intro a.
pose representative i := proj1_sig (constructive_indefinite_description (quotient_pi_surjective (a i))).
have hr i : quotient_pi (boundaries_in_cycles (K i) n) (representative i) = a i :=
  proj2_sig (constructive_indefinite_description (quotient_pi_surjective (a i))).
pose x : product_term n := fun i => cycle_inclusion (K i) n (representative i).
have hx : cocycle product_complex n x.
  apply functional_extensionality_dep; intro i; exact (submodule_val_mem (representative i)).
exists (cohomology_class hx).
apply functional_extensionality_dep; intro i.
change (cohomology_map (product_projection i) n (cohomology_class hx) = a i).
rewrite cohomology_map_class -hr.
unfold cohomology_class; congr (quotient_pi _ _).
apply submodule_val_injective; reflexivity.
Qed.

Definition product_cohomology_iso n : @isomorphism (module_category R)
    (cohomology product_complex n) (product_cohomology_term n) :=
  @linear_bijection_iso R (cohomology product_complex n) (product_cohomology_term n)
    (@product_cohomology_at n : {linear _ -> _})
    (@product_cohomology_injective n) (@product_cohomology_surjective n).

Theorem product_cohomology_iso_component n (a : cohomology product_complex n) i :
    module_hom_fun (iso_hom (product_cohomology_iso n)) a i =
      cohomology_map (product_projection i) n a.
Proof. reflexivity. Qed.
End Product.
End DPCochainProduct.
