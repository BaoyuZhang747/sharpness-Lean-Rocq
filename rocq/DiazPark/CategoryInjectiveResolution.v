(** Actual augmented injective resolutions, formed by repeatedly embedding
    the successive cokernel diagrams. No differential or exactness theorem
    is supplied as a construction parameter. *)
From mathcomp Require Import all_ssreflect ssralg.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInjectives CategoryDiagramEnoughInjectives CategoryDiagramCokernel
  HomologicalDiagramInjectives.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Record injective_resolution {R : pzRingType} {C : category}
    (F : module_diagram R C) := {
  injective_resolution_complex : @diagram_complex R C;
  injective_resolution_augmentation : nat_trans F
    (diagram_term injective_resolution_complex 0%N);
  injective_resolution_term_injective : forall n,
    injective_object (functor_category C (module_category R))
      (diagram_term injective_resolution_complex n);
  injective_resolution_augmentation_injective : forall x,
    injective (module_hom_fun (component injective_resolution_augmentation x));
  injective_resolution_augmentation_zero : forall x (v : fobj F x),
    module_hom_fun (component (diagram_d injective_resolution_complex 0%N) x)
      (module_hom_fun (component injective_resolution_augmentation x) v) = 0;
  injective_resolution_exact_zero : forall x
    (v : fobj (diagram_term injective_resolution_complex 0%N) x),
    module_hom_fun (component (diagram_d injective_resolution_complex 0%N) x) v = 0 <->
    exists u, module_hom_fun (component injective_resolution_augmentation x) u = v;
  injective_resolution_exact_successor : forall n x
    (v : fobj (diagram_term injective_resolution_complex n.+1) x),
    module_hom_fun (component (diagram_d injective_resolution_complex n.+1) x) v = 0 ->
    exists u, module_hom_fun (component (diagram_d injective_resolution_complex n) x) u = v
}.

Arguments injective_resolution_complex {R C F} _.
Arguments injective_resolution_augmentation {R C F} _.
Arguments injective_resolution_term_injective {R C F} _ n.
Arguments injective_resolution_augmentation_injective {R C F} _ x.
Arguments injective_resolution_augmentation_zero {R C F} _ x v.
Arguments injective_resolution_exact_zero {R C F} _ x v.
Arguments injective_resolution_exact_successor {R C F} _ n x v _.

Section ResolutionConstruction.
Variable R : pzRingType.
Variable C : category.
Variable choose : forall F : module_diagram R C, diagram_injective_embedding F.
Variable F : module_diagram R C.

Fixpoint resolution_syzygy (n : nat) : module_diagram R C :=
  match n with
  | 0%N => F
  | k.+1 => diagram_cokernel (diagram_embedding_map (choose (resolution_syzygy k)))
  end.

Definition resolution_embedding n := choose (resolution_syzygy n).
Definition resolution_injective_term n := diagram_embedding_target (resolution_embedding n).
Definition resolution_to_syzygy n :
    nat_trans (resolution_injective_term n) (resolution_syzygy n.+1) :=
  diagram_cokernel_projection (diagram_embedding_map (resolution_embedding n)).

Definition resolution_differential n :
    nat_trans (resolution_injective_term n) (resolution_injective_term n.+1) :=
  nat_comp (resolution_to_syzygy n) (diagram_embedding_map (resolution_embedding n.+1)).

Lemma resolution_differential_kernel n x (v : fobj (resolution_injective_term n) x) :
    module_hom_fun (component (resolution_differential n) x) v = 0 <->
    exists u, module_hom_fun (component (diagram_embedding_map (resolution_embedding n)) x) u = v.
Proof.
  split.
  - intro hv.
    apply (proj1 (@diagram_cokernel_exact R C (resolution_syzygy n)
      (resolution_injective_term n) (diagram_embedding_map (resolution_embedding n)) x v)).
    apply (diagram_embedding_pointwise_injective (resolution_embedding n.+1) x).
    change (module_hom_fun (component (resolution_differential n) x) v =
      module_hom_fun (component (diagram_embedding_map (resolution_embedding n.+1)) x) 0).
    rewrite module_hom_zero. exact hv.
  - intro hv.
    pose proof ((proj2 (@diagram_cokernel_exact R C (resolution_syzygy n)
      (resolution_injective_term n) (diagram_embedding_map (resolution_embedding n)) x v)) hv) as h.
    change (module_hom_fun (component (diagram_embedding_map (resolution_embedding n.+1)) x)
      (module_hom_fun (component (resolution_to_syzygy n) x) v) = 0).
    change (module_hom_fun (component (resolution_to_syzygy n) x) v = 0) in h.
    rewrite h. apply module_hom_zero.
Qed.

Lemma resolution_differential_squared n x (v : fobj (resolution_injective_term n) x) :
    module_hom_fun (component (resolution_differential n.+1) x)
      (module_hom_fun (component (resolution_differential n) x) v) = 0.
Proof.
  apply (proj2 (resolution_differential_kernel _)).
  exists (module_hom_fun (component (resolution_to_syzygy n) x) v). reflexivity.
Qed.

Definition constructed_injective_complex : @diagram_complex R C :=
  @DiagramComplex R C resolution_injective_term resolution_differential
    resolution_differential_squared.

Definition constructed_augmentation : nat_trans F (resolution_injective_term 0%N) :=
  diagram_embedding_map (resolution_embedding 0%N).

Lemma constructed_augmentation_zero x (v : fobj F x) :
    module_hom_fun (component (resolution_differential 0%N) x)
      (module_hom_fun (component constructed_augmentation x) v) = 0.
Proof. apply (proj2 (resolution_differential_kernel _)). exists v. reflexivity. Qed.

Lemma constructed_resolution_exact_successor n x
    (v : fobj (resolution_injective_term n.+1) x) :
    module_hom_fun (component (resolution_differential n.+1) x) v = 0 ->
    exists u, module_hom_fun (component (resolution_differential n) x) u = v.
Proof.
  intro hv. destruct ((proj1 (resolution_differential_kernel v)) hv) as [u hu].
  destruct (@diagram_cokernel_surjective R C (resolution_syzygy n)
    (resolution_injective_term n) (diagram_embedding_map (resolution_embedding n)) x u)
    as [w hw].
  exists w.
  change (module_hom_fun (component (diagram_embedding_map (resolution_embedding n.+1)) x)
    (module_hom_fun (component (resolution_to_syzygy n) x) w) = v).
  change (module_hom_fun (component (resolution_to_syzygy n) x) w = u) in hw.
  rewrite hw. exact hu.
Qed.

Definition injective_resolution_from_embeddings : injective_resolution F.
Proof.
  refine (@Build_injective_resolution R C F constructed_injective_complex
    constructed_augmentation (fun n => diagram_embedding_injective (resolution_embedding n))
    (diagram_embedding_pointwise_injective (resolution_embedding 0%N))
    constructed_augmentation_zero _ constructed_resolution_exact_successor).
  intros x v. exact (resolution_differential_kernel v).
Defined.
End ResolutionConstruction.

Arguments injective_resolution_from_embeddings {R C} choose F.
