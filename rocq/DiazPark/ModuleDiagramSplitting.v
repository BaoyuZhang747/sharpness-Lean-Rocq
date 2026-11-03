(** A short exact sequence of arbitrary module diagrams splits naturally
    when its first term is injective in the diagram category. *)

From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInjectives ModuleDiagrams ModuleDiagramDescent.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Splitting.
Variable R : pzRingType.
Variable C : category.
Variables A B D : module_diagram R C.
Variables (i : nat_trans A B) (q : nat_trans B D).
Hypothesis ii : forall x, injective (module_hom_fun (component i x)).
Hypothesis eqi : forall x (v : fobj B x), module_hom_fun (component q x) v = 0 <->
  exists u : fobj A x, module_hom_fun (component i x) u = v.
Hypothesis qs : forall x (v : fobj D x), exists u : fobj B x,
  module_hom_fun (component q x) u = v.

Arguments eqi x v : clear implicits.
Arguments qs x v : clear implicits.

Variable r : nat_trans B A.
Hypothesis ri : forall x (v : fobj A x),
  module_hom_fun (component r x) (module_hom_fun (component i x) v) = v.
Arguments ri x v : clear implicits.

Definition split_projection_component (x : C) : module_hom (fobj B x) (fobj B x).
Proof.
  exists (fun v => v - module_hom_fun (component i x)
    (module_hom_fun (component r x) v)).
  intros a u v. rewrite !module_hom_linear scalerBr.
  by rewrite opprD addrACA.
Defined.

Definition split_projection : nat_trans B B.
Proof.
  refine (@Build_nat_trans C (module_category R) B B split_projection_component _).
  intros x y f. apply module_hom_ext. intro v.
  pose proof (f_equal (fun k : module_hom (fobj B x) (fobj A y) => k v)
    (naturality r f)) as hr.
  pose proof (f_equal (fun k : module_hom (fobj A x) (fobj B y) =>
      k (module_hom_fun (component r x) v)) (naturality i f)) as hi.
  change (module_hom_fun (fmap B f) v -
      module_hom_fun (component i y)
        (module_hom_fun (component r y) (module_hom_fun (fmap B f) v)) =
    module_hom_fun (fmap B f)
      (v - module_hom_fun (component i x) (module_hom_fun (component r x) v))).
  rewrite module_hom_sub. apply f_equal. apply f_equal.
  transitivity (module_hom_fun (component i y)
    (module_hom_fun (fmap A f) (module_hom_fun (component r x) v))).
  - exact (f_equal (module_hom_fun (component i y)) hr).
  - exact hi.
Defined.

Lemma split_projection_kernel x (v : fobj B x) :
    module_hom_fun (component q x) v = 0 ->
    module_hom_fun (component split_projection x) v = 0.
Proof.
  intro hv. destruct ((proj1 (eqi x v)) hv) as [u <-].
  change (module_hom_fun (component i x) u -
    module_hom_fun (component i x)
      (module_hom_fun (component r x) (module_hom_fun (component i x) u)) = 0).
  by rewrite ri subrr.
Qed.

Definition split_section : nat_trans D B :=
  @diagram_descent R C B D B q split_projection qs split_projection_kernel.

Lemma split_section_factor x (v : fobj B x) :
    module_hom_fun (component split_section x) (module_hom_fun (component q x) v) =
    v - module_hom_fun (component i x) (module_hom_fun (component r x) v).
Proof. exact (@diagram_descent_factor R C B D B q split_projection qs
  split_projection_kernel x v). Qed.

Lemma split_section_retraction x (v : fobj D x) :
    module_hom_fun (component q x) (module_hom_fun (component split_section x) v) = v.
Proof.
  destruct (qs x v) as [u <-]. rewrite split_section_factor module_hom_sub.
  assert (module_hom_fun (component q x)
    (module_hom_fun (component i x) (module_hom_fun (component r x) u)) = 0) as h.
  { apply (proj2 (eqi x _)). by exists (module_hom_fun (component r x) u). }
  by rewrite h subr0.
Qed.

Lemma split_section_decomposition x (v : fobj B x) :
    module_hom_fun (component i x) (module_hom_fun (component r x) v) +
      module_hom_fun (component split_section x) (module_hom_fun (component q x) v) = v.
Proof. rewrite split_section_factor addrC. apply subrK. Qed.

End Splitting.

Section InjectiveSplitting.
Variable R : pzRingType.
Variable C : category.
Variables A B D : module_diagram R C.
Variables (i : nat_trans A B) (q : nat_trans B D).
Hypothesis ii : forall x, injective (module_hom_fun (component i x)).
Hypothesis eqi : forall x (v : fobj B x), module_hom_fun (component q x) v = 0 <->
  exists u : fobj A x, module_hom_fun (component i x) u = v.
Hypothesis qs : forall x (v : fobj D x), exists u : fobj B x,
  module_hom_fun (component q x) u = v.

Theorem injective_diagram_short_exact_split :
    injective_object (functor_category C (module_category R)) A ->
    exists (r : nat_trans B A) (s : nat_trans D B),
    (forall x v, module_hom_fun (component r x) (module_hom_fun (component i x) v) = v) /\
    (forall x v, module_hom_fun (component q x) (module_hom_fun (component s x) v) = v) /\
    (forall x v, module_hom_fun (component i x) (module_hom_fun (component r x) v) +
      module_hom_fun (component s x) (module_hom_fun (component q x) v) = v).
Proof.
  intro hA. destruct (hA A B i (pointwise_injective_monomorphism ii) (nat_id A)) as [r hr].
  assert (forall x v, module_hom_fun (component r x)
    (module_hom_fun (component i x) v) = v) as ri.
  { intros x v. exact (f_equal (fun k : nat_trans A A =>
      module_hom_fun (component k x) v) hr). }
  exists r. exists (@split_section R C A B D i q eqi qs r ri). split.
  - exact ri.
  - split.
    + exact (@split_section_retraction R C A B D i q eqi qs r ri).
    + exact (@split_section_decomposition R C A B D i q eqi qs r ri).
Qed.

Theorem split_diagram_successor_injective :
    injective_object (functor_category C (module_category R)) A ->
    injective_object (functor_category C (module_category R)) B ->
    injective_object (functor_category C (module_category R)) D.
Proof.
  intros hA hB.
  destruct (injective_diagram_short_exact_split hA) as [r [s [ri [qs1 h]]]].
  apply (@injective_retract (functor_category C (module_category R)) D B s q).
  - apply nat_trans_ext. intro x. apply module_hom_ext. apply qs1.
  - exact hB.
Qed.

End InjectiveSplitting.
