(** Actual quotient diagrams and cokernels, on arbitrary module carriers. *)
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleLinear ModuleInfrastructure MackeyModuleQuotient
  MackeyModuleMaps ModuleDiagrams ModuleDiagramDescent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section DiagramQuotient.
Variable R : pzRingType.
Variable C : category.
Variable F : module_diagram R C.
Variable N : forall x, module_subspace (fobj F x).
Hypothesis hN : forall x y (f : hom C x y) v,
  N x v -> N y (module_hom_fun (fmap F f) v).

Definition diagram_quotient_object (x : C) : lmodType R :=
  [the lmodType R of module_quotient (N x)].

Definition diagram_quotient_map {x y : C} (f : hom C x y) :
    module_hom (diagram_quotient_object x) (diagram_quotient_object y) :=
  module_hom_of_linear (@quotient_map R (fobj F x) (fobj F y)
    (module_hom_to_linear (fmap F f)) (N x) (N y) (@hN x y f)).

Lemma diagram_quotient_map_pi x y (f : hom C x y) v :
    diagram_quotient_map f (quotient_pi (N x) v) =
      quotient_pi (N y) (module_hom_fun (fmap F f) v).
Proof. exact (@quotient_map_pi R (fobj F x) (fobj F y)
  (module_hom_to_linear (fmap F f)) (N x) (N y) (@hN x y f) v). Qed.

Definition diagram_quotient : module_diagram R C.
Proof.
  refine (@Build_functor C (module_category R) diagram_quotient_object
    (fun x y f => diagram_quotient_map f) _ _).
  - intro x. apply module_hom_ext. intro v.
    destruct (quotient_pi_surjective (N := N x) v) as [u <-].
    change (diagram_quotient_map (identity x) (quotient_pi (N x) u) = quotient_pi (N x) u).
    rewrite diagram_quotient_map_pi fmap_id. reflexivity.
  - intros x y z f g. apply module_hom_ext. intro v.
    destruct (quotient_pi_surjective (N := N x) v) as [u <-].
    change (diagram_quotient_map (compose f g) (quotient_pi (N x) u) =
      diagram_quotient_map g (diagram_quotient_map f (quotient_pi (N x) u))).
    rewrite !diagram_quotient_map_pi fmap_compose. reflexivity.
Defined.

Definition diagram_quotient_projection : nat_trans F diagram_quotient.
Proof.
  refine (@Build_nat_trans C (module_category R) F diagram_quotient
    (fun x => module_hom_of_linear
      (quotient_pi (N x) : {linear fobj F x -> diagram_quotient_object x})) _).
  intros x y f. apply module_hom_ext. intro v. symmetry.
  exact (diagram_quotient_map_pi f v).
Defined.

Lemma diagram_quotient_projection_surjective x (v : fobj diagram_quotient x) :
  exists u, module_hom_fun (component diagram_quotient_projection x) u = v.
Proof. exact (quotient_pi_surjective v). Qed.

Lemma diagram_quotient_projection_kernel x v :
  module_hom_fun (component diagram_quotient_projection x) v = 0 <-> N x v.
Proof. exact (quotient_pi_kernel (N x) v). Qed.
End DiagramQuotient.

Section DiagramCokernel.
Variable R : pzRingType.
Variable C : category.
Variables F G : module_diagram R C.
Variable m : nat_trans F G.

Definition diagram_image_subspace (x : C) : module_subspace (fobj G x) :=
  linear_image (module_hom_to_linear (component m x)).

Lemma diagram_image_stable x y (f : hom C x y) v :
  diagram_image_subspace x v ->
    diagram_image_subspace y (module_hom_fun (fmap G f) v).
Proof.
  intros [u <-]. exists (module_hom_fun (fmap F f) u).
  exact (f_equal (fun k : module_hom (fobj F x) (fobj G y) => k u) (naturality m f)).
Qed.

Definition diagram_cokernel : module_diagram R C :=
  @diagram_quotient R C G diagram_image_subspace (@diagram_image_stable).

Definition diagram_cokernel_projection : nat_trans G diagram_cokernel :=
  @diagram_quotient_projection R C G diagram_image_subspace (@diagram_image_stable).

Lemma diagram_cokernel_surjective x (v : fobj diagram_cokernel x) :
  exists u, module_hom_fun (component diagram_cokernel_projection x) u = v.
Proof. exact (quotient_pi_surjective v). Qed.

Lemma diagram_cokernel_exact x v :
  module_hom_fun (component diagram_cokernel_projection x) v = 0 <->
    exists u, module_hom_fun (component m x) u = v.
Proof. exact (quotient_pi_kernel (diagram_image_subspace x) v). Qed.

Lemma diagram_cokernel_zero x v :
  module_hom_fun (component diagram_cokernel_projection x)
    (module_hom_fun (component m x) v) = 0.
Proof. apply (proj2 (diagram_cokernel_exact _)). exists v. reflexivity. Qed.

Definition diagram_cokernel_desc (H : module_diagram R C) (t : nat_trans G H)
    (ht : forall x v, module_hom_fun (component t x)
      (module_hom_fun (component m x) v) = 0) : nat_trans diagram_cokernel H.
Proof.
  refine (@diagram_descent R C G diagram_cokernel H diagram_cokernel_projection t
    diagram_cokernel_surjective _).
  intros x v hv. destruct ((proj1 (diagram_cokernel_exact v)) hv) as [u <-].
  exact (ht x u).
Defined.

Lemma diagram_cokernel_desc_fac (H : module_diagram R C) (t : nat_trans G H)
    (ht : forall x v, module_hom_fun (component t x)
      (module_hom_fun (component m x) v) = 0) :
  nat_comp diagram_cokernel_projection (diagram_cokernel_desc ht) = t.
Proof. apply diagram_descent_fac. Qed.

Lemma diagram_cokernel_desc_unique (H : module_diagram R C) (t : nat_trans G H)
    (ht : forall x v, module_hom_fun (component t x)
      (module_hom_fun (component m x) v) = 0)
    (s : nat_trans diagram_cokernel H) :
  nat_comp diagram_cokernel_projection s = t -> s = diagram_cokernel_desc ht.
Proof. apply diagram_descent_unique. Qed.
End DiagramCokernel.

Arguments diagram_cokernel {R C F G} m.
Arguments diagram_cokernel_projection {R C F G} m.
