(** Actual kernel/image homology for the constructed page differential.
    Incoming maps use explicit integer-index transport; at degree zero
    there are no incoming boundaries. *)
From Coq Require Import ZArith Lia.
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient
  MackeyModuleMaps HomologicalComplex.
From DiazParkV16b Require Import FilteredCochainCycles FilteredCochainPages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DPFilteredCycles DPFilteredPages.
Local Open Scope ring_scope.

Module DPFilteredPageHomology.
Section Homology.
Variable R : pzRingType.
Variable C : cochain_complex R.
Variable F : cochain_filtration C.

Definition page_index_cast r p q n (h : p=q) : {linear page F r p n -> page F r q n}.
Proof. destruct h; exact (idfun : {linear page F r p n -> page F r p n}). Defined.

Lemma page_index_cast_pi r p q n (h : p=q) (x : page_cycle_module F r p n) :
    page_index_cast r n h (quotient_pi (page_denominator F r p n) x) =
      quotient_pi (page_denominator F r q n)
        (eq_rect p (fun t => page_cycle_module F r t n) x q h).
Proof. destruct h; reflexivity. Qed.

Definition incoming_index r p : Z.add (Z.sub p (Z.of_nat r.+1)) (Z.of_nat r.+1) = p.
Proof. lia. Qed.

Definition page_incoming r p n (x : page F r (Z.sub p (Z.of_nat r.+1)) n) : page F r p n.+1 :=
  page_index_cast r n.+1 (incoming_index r p) (page_d F r (Z.sub p (Z.of_nat r.+1)) n x).

Lemma page_incoming_linear r p n : linear (@page_incoming r p n).
Proof. intros a x y; by rewrite /page_incoming !linearP. Qed.
HB.instance Definition _ r p n := GRing.isLinear.Build R (page F r (Z.sub p (Z.of_nat r.+1)) n)
  (page F r p n.+1) _ (@page_incoming r p n) (@page_incoming_linear r p n).

Lemma page_cast_d_zero r p q n (h : p=q) (x : page F r p n) :
    page_d F r p n x = 0 -> page_d F r q n (page_index_cast r n h x) = 0.
Proof. destruct h; exact (fun h => h). Qed.

Lemma page_incoming_cycle r p n x : page_d F r p n.+1 (page_incoming x) = 0.
Proof.
exact (@page_cast_d_zero r (Z.add (Z.sub p (Z.of_nat r.+1)) (Z.of_nat r.+1)) p n.+1
  (incoming_index r p) (page_d F r (Z.sub p (Z.of_nat r.+1)) n x)
  (@page_d_squared R C F r (Z.sub p (Z.of_nat r.+1)) n x)).
Qed.

Definition page_homology_cycles r p n : lmodType R := submodule_carrier (linear_kernel (page_d F r p n)).

Definition page_boundaries r p n : module_subspace (page F r p n) :=
  match n as k return module_subspace (page F r p k) with
  | O => subspace_zero_space (page F r p O)
  | S k => linear_image (@page_incoming r p k)
  end.

Lemma page_boundaries_cycles r p n : subspace_le (page_boundaries r p n) (linear_kernel (page_d F r p n)).
Proof.
destruct n; simpl.
- intros x hx; change (x=0) in hx; change (page_d F r p 0%N x=0); by rewrite hx linear0.
- intros x [y <-]; exact: page_incoming_cycle.
Qed.

Definition page_homology_relations r p n : module_subspace (page_homology_cycles r p n) :=
  linear_preimage (submodule_inclusion (linear_kernel (page_d F r p n))) (page_boundaries r p n).

Definition page_homology r p n : lmodType R := module_quotient (page_homology_relations r p n).

End Homology.
End DPFilteredPageHomology.
