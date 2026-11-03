(** A projective resolution of every arbitrary module diagram, constructed
    by repeatedly covering the actual kernel diagram. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  ModuleDiagrams MackeyModuleCarriers CategoryEnoughProjectives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPEnoughProjectives.
Local Open Scope ring_scope.

Module DPEnoughProjectiveResolutions.
Record projective_resolution {R : pzRingType} {C : category} (F : module_diagram R C) := {
  projective_term : nat -> module_diagram R C;
  projective_d : forall n, nat_trans (projective_term n.+1) (projective_term n);
  projective_augmentation : nat_trans (projective_term 0%N) F;
  projective_terms_projective : forall n,
    projective_object (functor_category C (module_category R)) (projective_term n);
  projective_augmentation_surjective : forall x (v : fobj F x), exists u,
    module_hom_fun (component projective_augmentation x) u = v;
  projective_d_squared : forall n x (v : fobj (projective_term n.+2) x),
    module_hom_fun (component (projective_d n) x)
      (module_hom_fun (component (projective_d n.+1) x) v) = 0;
  projective_augmentation_zero : forall x (v : fobj (projective_term 1%N) x),
    module_hom_fun (component projective_augmentation x)
      (module_hom_fun (component (projective_d 0%N) x) v) = 0;
  projective_exact_augmentation : forall x (v : fobj (projective_term 0%N) x),
    module_hom_fun (component projective_augmentation x) v = 0 <->
    exists u, module_hom_fun (component (projective_d 0%N) x) u = v;
  projective_exact_successor : forall n x (v : fobj (projective_term n.+1) x),
    module_hom_fun (component (projective_d n) x) v = 0 <->
    exists u, module_hom_fun (component (projective_d n.+1) x) u = v
}.
Arguments projective_term {R C F} _ n.
Arguments projective_d {R C F} _ n.
Arguments projective_augmentation {R C F} _.
Arguments projective_terms_projective {R C F} _ n.
Arguments projective_augmentation_surjective {R C F} _ x v.

Section Construction.
Variable R : pzRingType.
Variable C : category.
Variable F : module_diagram R C.
Fixpoint syzygy (n : nat) : module_diagram R C :=
  match n with
  | 0%N => F
  | k.+1 => diagram_kernel (projective_cover_map (syzygy k))
  end.
Definition term n := projective_cover (syzygy n).
Definition onto_syzygy n : nat_trans (term n) (syzygy n) := projective_cover_map (syzygy n).
Definition kernel_inclusion n : nat_trans (syzygy n.+1) (term n) :=
  diagram_kernel_inclusion (onto_syzygy n).
Definition differential n : nat_trans (term n.+1) (term n) :=
  nat_comp (onto_syzygy n.+1) (kernel_inclusion n).
Definition augmentation : nat_trans (term 0%N) F := onto_syzygy 0%N.

Lemma kernel_inclusion_injective n x :
  injective (module_hom_fun (component (kernel_inclusion n) x)).
Proof. exact: diagram_kernel_inclusion_injective. Qed.
Lemma onto_differential_zero n x (v : fobj (term n.+1) x) :
  module_hom_fun (component (onto_syzygy n) x)
    (module_hom_fun (component (differential n) x) v) = 0.
Proof.
change (module_hom_fun (component (onto_syzygy n) x)
  (submodule_val (module_hom_fun (component (onto_syzygy n.+1) x) v)) = 0).
exact (submodule_val_mem (module_hom_fun (component (onto_syzygy n.+1) x) v)).
Qed.
Lemma onto_differential_exact n x (v : fobj (term n) x) :
  module_hom_fun (component (onto_syzygy n) x) v = 0 <->
  exists u, module_hom_fun (component (differential n) x) u = v.
Proof.
split.
- move=> hv.
  pose z := @submodule_in R (fobj (term n) x)
    (diagram_kernel_subspace (onto_syzygy n) x) v hv.
  have [u hu] := @projective_cover_surjective R C (syzygy n.+1) x z.
  exists u.
  change (module_hom_fun (component (kernel_inclusion n) x)
    (module_hom_fun (component (onto_syzygy n.+1) x) u) = v).
  change (module_hom_fun (component (onto_syzygy n.+1) x) u = z) in hu.
  by rewrite hu.
- move=> [u <-]; exact: onto_differential_zero.
Qed.
Lemma differential_kernel n x (v : fobj (term n.+1) x) :
  module_hom_fun (component (differential n) x) v = 0 <->
  module_hom_fun (component (onto_syzygy n.+1) x) v = 0.
Proof.
split.
- move=> hv; apply: (@kernel_inclusion_injective n x).
  change (module_hom_fun (component (differential n) x) v =
    module_hom_fun (component (kernel_inclusion n) x) 0).
  by rewrite hv module_hom_zero.
- move=> hv; change (module_hom_fun (component (kernel_inclusion n) x)
    (module_hom_fun (component (onto_syzygy n.+1) x) v) = 0).
  by rewrite hv module_hom_zero.
Qed.
Lemma differential_squared n x (v : fobj (term n.+2) x) :
  module_hom_fun (component (differential n) x)
    (module_hom_fun (component (differential n.+1) x) v) = 0.
Proof. apply/(differential_kernel _); exact: onto_differential_zero. Qed.
Lemma differential_exact n x (v : fobj (term n.+1) x) :
  module_hom_fun (component (differential n) x) v = 0 <->
  exists u, module_hom_fun (component (differential n.+1) x) u = v.
Proof. rewrite differential_kernel; exact: onto_differential_exact. Qed.

Definition constructed_projective_resolution : projective_resolution F :=
  @Build_projective_resolution R C F term differential augmentation
    (fun n => @projective_cover_projective R C (syzygy n))
    (@projective_cover_surjective R C F)
    (@differential_squared) (@onto_differential_zero 0%N)
    (@onto_differential_exact 0%N) (@differential_exact).
End Construction.

Theorem projective_resolution_exists (R : pzRingType) (C : category)
    (F : module_diagram R C) : exists P : projective_resolution F, True.
Proof. exists (constructed_projective_resolution F); exact I. Qed.
End DPEnoughProjectiveResolutions.



