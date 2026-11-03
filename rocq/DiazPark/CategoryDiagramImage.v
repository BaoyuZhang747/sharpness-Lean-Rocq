(** Actual image diagrams and extension across a map into an injective
    diagram whenever the prescribed map kills its kernel. *)
From mathcomp Require Import all_ssreflect all_algebra.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInjectives CategoryDiagramCokernel ModuleDiagrams ModuleDiagramDescent
  ModuleInfrastructure MackeyModuleCarriers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Images.
Variable R : pzRingType.
Variable C : category.
Variables F G : module_diagram R C.
Variable m : nat_trans F G.

Definition diagram_image : module_diagram R C :=
  @subdiagram R C G (diagram_image_subspace m) (@diagram_image_stable R C F G m).

Definition diagram_image_inclusion : nat_trans diagram_image G :=
  @subdiagram_inclusion R C G (diagram_image_subspace m) (@diagram_image_stable R C F G m).

Definition diagram_image_projection : nat_trans F diagram_image :=
  @subdiagram_lift R C G (diagram_image_subspace m) (@diagram_image_stable R C F G m)
    F m (fun x v => ex_intro _ v (Logic.eq_refl _)).

Lemma diagram_image_projection_surjective x (v : fobj diagram_image x) :
    exists u, module_hom_fun (component diagram_image_projection x) u = v.
Proof.
  destruct (submodule_val_mem v) as [u hu]. exists u.
  apply submodule_val_injective. exact hu.
Qed.

Lemma diagram_image_projection_zero x v :
    module_hom_fun (component diagram_image_projection x) v = 0 ->
    module_hom_fun (component m x) v = 0.
Proof.
  intro h. exact (f_equal
    (@submodule_val R (fobj G x) (diagram_image_subspace m x)) h).
Qed.

Lemma diagram_image_factor : nat_comp diagram_image_projection diagram_image_inclusion = m.
Proof. apply nat_trans_ext. intro x. apply module_hom_ext. intro v. reflexivity. Qed.

Theorem injective_diagram_factor (J : module_diagram R C)
    (hJ : injective_object (functor_category C (module_category R)) J)
    (t : nat_trans F J)
    (ht : forall x v, module_hom_fun (component m x) v = 0 ->
      module_hom_fun (component t x) v = 0) :
    exists s : nat_trans G J, nat_comp m s = t.
Proof.
  pose (k := @diagram_descent R C F diagram_image J diagram_image_projection t
    diagram_image_projection_surjective
    (fun x v h => ht x v (diagram_image_projection_zero h))).
  assert (hm : @monomorphism (functor_category C (module_category R))
    diagram_image G diagram_image_inclusion).
  { apply pointwise_injective_monomorphism. intro x.
    exact (@subdiagram_inclusion_injective R C G (diagram_image_subspace m)
      (@diagram_image_stable R C F G m) x). }
  destruct (hJ diagram_image G diagram_image_inclusion hm k) as [s hs].
  exists s. apply nat_trans_ext. intro x. apply module_hom_ext. intro v.
  pose proof (f_equal (fun a : nat_trans diagram_image J =>
    module_hom_fun (component a x)
      (module_hom_fun (component diagram_image_projection x) v)) hs) as h.
  transitivity (module_hom_fun (component k x)
    (module_hom_fun (component diagram_image_projection x) v)).
  - exact h.
  - exact (@diagram_descent_factor R C F diagram_image J diagram_image_projection t
      diagram_image_projection_surjective
      (fun x v h => ht x v (diagram_image_projection_zero h)) x v).
Qed.
End Images.
