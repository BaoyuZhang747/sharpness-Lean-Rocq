(** The split-exact step in the spectral-sequence-free fiber argument.
    Exactness includes degree zero. Every splitting is a natural map of
    actual arbitrary module diagrams. *)

From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryInjectives ModuleInfrastructure MackeyModuleCarriers
  ModuleDiagrams ModuleDiagramSplitting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section DiagramComplexes.
Variable R : pzRingType.
Variable C : category.

Record diagram_complex := DiagramComplex {
  diagram_term : nat -> module_diagram R C;
  diagram_d : forall n, nat_trans (diagram_term n) (diagram_term n.+1);
  diagram_d2 : forall n x (v : fobj (diagram_term n) x),
    module_hom_fun (component (diagram_d n.+1) x)
      (module_hom_fun (component (diagram_d n) x) v) = 0
}.

Arguments diagram_d2 d n x v : clear implicits.

Definition diagram_all_exact (K : diagram_complex) : Prop :=
  (forall x (v : fobj (diagram_term K 0%N) x),
    module_hom_fun (component (diagram_d K 0%N) x) v = 0 -> v = 0) /\
  (forall n x (v : fobj (diagram_term K n.+1) x),
    module_hom_fun (component (diagram_d K n.+1) x) v = 0 ->
    exists u, module_hom_fun (component (diagram_d K n) x) u = v).

Definition diagram_cycles (K : diagram_complex) n := diagram_kernel (diagram_d K n).

Definition diagram_cycle_inclusion (K : diagram_complex) n :
    nat_trans (diagram_cycles K n) (diagram_term K n) :=
  diagram_kernel_inclusion (diagram_d K n).

Definition diagram_cycle_d (K : diagram_complex) n :
    nat_trans (diagram_term K n) (diagram_cycles K n.+1) :=
  @subdiagram_lift R C (diagram_term K n.+1)
    (diagram_kernel_subspace (diagram_d K n.+1))
    (@diagram_kernel_stable R C (diagram_term K n.+1) (diagram_term K n.+2)
      (diagram_d K n.+1))
    (diagram_term K n) (diagram_d K n) (fun x v => diagram_d2 K n x v).

Lemma diagram_cycle_d_val (K : diagram_complex) n x (v : fobj (diagram_term K n) x) :
    submodule_val (module_hom_fun (component (diagram_cycle_d K n) x) v) =
    module_hom_fun (component (diagram_d K n) x) v.
Proof. reflexivity. Qed.

Lemma diagram_cycle_exact (K : diagram_complex) n x (v : fobj (diagram_term K n) x) :
    module_hom_fun (component (diagram_cycle_d K n) x) v = 0 <->
    exists u, module_hom_fun (component (diagram_cycle_inclusion K n) x) u = v.
Proof.
  split.
  - intro hv.
    assert (module_hom_fun (component (diagram_d K n) x) v = 0) as hz.
    { exact (f_equal (@submodule_val R (fobj (diagram_term K n.+1) x)
        (diagram_kernel_subspace (diagram_d K n.+1) x)) hv). }
    exists (@submodule_in R (fobj (diagram_term K n) x)
      (diagram_kernel_subspace (diagram_d K n) x) v hz). reflexivity.
  - intros [u <-]. apply submodule_val_injective.
    exact (submodule_val_mem u).
Qed.

Lemma diagram_cycle_surjective (K : diagram_complex) (hK : diagram_all_exact K)
    n x (v : fobj (diagram_cycles K n.+1) x) :
    exists u, module_hom_fun (component (diagram_cycle_d K n) x) u = v.
Proof.
  destruct ((proj2 hK) n x (submodule_val v) (submodule_val_mem v)) as [u hu].
  exists u. apply submodule_val_injective. exact hu.
Qed.

Lemma zero_diagram_injective (F : module_diagram R C)
    (hF : forall x (v : fobj F x), v = 0) :
    injective_object (functor_category C (module_category R)) F.
Proof.
  intros A B m hm f. exists (diagram_zero B F).
  apply nat_trans_ext. intro x. apply module_hom_ext. intro v.
  symmetry. exact (hF x (module_hom_fun (component f x) v)).
Qed.

Lemma exact_diagram_cycles_injective (K : diagram_complex)
    (hK : diagram_all_exact K)
    (hI : forall n, injective_object (functor_category C (module_category R))
      (diagram_term K n)) :
    forall n, injective_object (functor_category C (module_category R)) (diagram_cycles K n).
Proof.
  intro n. induction n as [|n ih].
  - apply zero_diagram_injective. intros x v. apply submodule_val_injective.
    exact ((proj1 hK) x (submodule_val v) (submodule_val_mem v)).
  - exact (@split_diagram_successor_injective R C (diagram_cycles K n)
      (diagram_term K n) (diagram_cycles K n.+1)
      (diagram_cycle_inclusion K n) (diagram_cycle_d K n)
      (fun x => @diagram_kernel_inclusion_injective R C (diagram_term K n) (diagram_term K n.+1) (diagram_d K n) x)
      (@diagram_cycle_exact K n) (@diagram_cycle_surjective K hK n) ih (hI n)).
Qed.

Record diagram_contraction (K : diagram_complex) := DiagramContraction {
  diagram_contraction_at : forall n, nat_trans (diagram_term K n.+1) (diagram_term K n);
  diagram_contraction_zero : forall x (v : fobj (diagram_term K 0%N) x),
    module_hom_fun (component (diagram_contraction_at 0%N) x)
      (module_hom_fun (component (diagram_d K 0%N) x) v) = v;
  diagram_contraction_succ : forall n x (v : fobj (diagram_term K n.+1) x),
    module_hom_fun (component (diagram_d K n) x)
      (module_hom_fun (component (diagram_contraction_at n) x) v) +
    module_hom_fun (component (diagram_contraction_at n.+1) x)
      (module_hom_fun (component (diagram_d K n.+1) x) v) = v
}.

Section ExactInjectives.
Variable K : diagram_complex.
Hypothesis hK : diagram_all_exact K.
Hypothesis hI : forall n, injective_object (functor_category C (module_category R))
  (diagram_term K n).

Definition cycle_split_property n
    (r : nat_trans (diagram_term K n) (diagram_cycles K n))
    (s : nat_trans (diagram_cycles K n.+1) (diagram_term K n)) : Prop :=
  (forall x v, module_hom_fun (component r x)
    (module_hom_fun (component (diagram_cycle_inclusion K n) x) v) = v) /\
  (forall x v, module_hom_fun (component (diagram_cycle_d K n) x)
    (module_hom_fun (component s x) v) = v) /\
  (forall x v, module_hom_fun (component (diagram_cycle_inclusion K n) x)
    (module_hom_fun (component r x) v) +
    module_hom_fun (component s x)
      (module_hom_fun (component (diagram_cycle_d K n) x) v) = v).

Arguments cycle_split_property n r s : clear implicits.

Lemma cycle_split_exists n : exists r s, cycle_split_property n r s.
Proof.
  exact (@injective_diagram_short_exact_split R C (diagram_cycles K n)
    (diagram_term K n) (diagram_cycles K n.+1)
    (diagram_cycle_inclusion K n) (diagram_cycle_d K n)
    (fun x => @diagram_kernel_inclusion_injective R C (diagram_term K n) (diagram_term K n.+1) (diagram_d K n) x)
    (@diagram_cycle_exact K n) (@diagram_cycle_surjective K hK n)
    (@exact_diagram_cycles_injective K hK hI n)).
Qed.

Definition cycle_retraction n :=
  proj1_sig (constructive_indefinite_description (cycle_split_exists n)).

Definition cycle_section n :=
  proj1_sig (constructive_indefinite_description
    (proj2_sig (constructive_indefinite_description (cycle_split_exists n)))).

Lemma cycle_split_spec n : cycle_split_property n (cycle_retraction n) (cycle_section n).
Proof.
  exact (proj2_sig (constructive_indefinite_description
    (proj2_sig (constructive_indefinite_description (cycle_split_exists n))))).
Qed.

Definition exact_diagram_contraction_at n :
    nat_trans (diagram_term K n.+1) (diagram_term K n) :=
  nat_comp (cycle_retraction n.+1) (cycle_section n).

Lemma exact_diagram_contraction_zero x (v : fobj (diagram_term K 0%N) x) :
    module_hom_fun (component (exact_diagram_contraction_at 0%N) x)
      (module_hom_fun (component (diagram_d K 0%N) x) v) = v.
Proof.
  pose proof ((proj1 (cycle_split_spec 1%N)) x
    (module_hom_fun (component (diagram_cycle_d K 0%N) x) v)) as hr.
  pose proof ((proj2 (proj2 (cycle_split_spec 0%N))) x v) as hd.
  assert (module_hom_fun (component (diagram_cycle_inclusion K 0%N) x)
    (module_hom_fun (component (cycle_retraction 0%N) x) v) = 0) as hz.
  { apply (proj1 hK). exact (submodule_val_mem
      (module_hom_fun (component (cycle_retraction 0%N) x) v)). }
  rewrite hz add0r in hd.
  change (module_hom_fun (component (cycle_section 0%N) x)
    (module_hom_fun (component (cycle_retraction 1%N) x)
      (module_hom_fun (component (diagram_d K 0%N) x) v)) = v).
  transitivity (module_hom_fun (component (cycle_section 0%N) x)
    (module_hom_fun (component (diagram_cycle_d K 0%N) x) v)).
  - apply f_equal. exact hr.
  - exact hd.
Qed.

Lemma exact_diagram_contraction_succ n x (v : fobj (diagram_term K n.+1) x) :
    module_hom_fun (component (diagram_d K n) x)
      (module_hom_fun (component (exact_diagram_contraction_at n) x) v) +
    module_hom_fun (component (exact_diagram_contraction_at n.+1) x)
      (module_hom_fun (component (diagram_d K n.+1) x) v) = v.
Proof.
  pose proof ((proj1 (proj2 (cycle_split_spec n))) x
    (module_hom_fun (component (cycle_retraction n.+1) x) v)) as hs.
  pose proof ((proj1 (cycle_split_spec n.+2)) x
    (module_hom_fun (component (diagram_cycle_d K n.+1) x) v)) as hr.
  transitivity (module_hom_fun (component (diagram_cycle_inclusion K n.+1) x)
    (module_hom_fun (component (cycle_retraction n.+1) x) v) +
    module_hom_fun (component (cycle_section n.+1) x)
      (module_hom_fun (component (diagram_cycle_d K n.+1) x) v)).
  - apply f_equal2.
    + exact (f_equal (module_hom_fun (component (diagram_cycle_inclusion K n.+1) x)) hs).
    + exact (f_equal (module_hom_fun (component (cycle_section n.+1) x)) hr).
  - exact ((proj2 (proj2 (cycle_split_spec n.+1))) x v).
Qed.

Definition exact_injective_diagram_contractible : diagram_contraction K :=
  @DiagramContraction K exact_diagram_contraction_at
    exact_diagram_contraction_zero exact_diagram_contraction_succ.

End ExactInjectives.
End DiagramComplexes.
