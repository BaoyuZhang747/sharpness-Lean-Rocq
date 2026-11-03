From mathcomp Require Import all_ssreflect fingroup perm morphism automorphism.
From mathcomp Require Import quotient cyclic pgroup sylow gproduct.
From DiazPark Require Import GroupQuotientInfrastructure GroupDeltaEmbedding.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

(** The displayed manuscript embedding for the kernel of an actual quotient
    action.  No displacement condition, injectivity, or p-kernel assertion
    is an input: each is deduced from the action formula below. *)
Section QuotientKernelDelta.
Variable gT : finGroupType.
Variables P Z : {group gT}.
Variable A : {group {perm gT}}.
Hypotheses (nZP : Z <| P) (cZP : Z \subset 'C(P)) (sAP : A \subset Aut P).
Hypothesis fixesZ : forall a, a \in A -> {in Z, a =1 id}.
Variable rho : {morphism A >-> {perm (coset_of Z)}}.
Hypothesis rho_action :
  forall a, a \in A -> forall x, x \in P ->
    rho a (coset Z x) = coset Z (a x).

Lemma quotient_kernel_sub_aut : 'ker rho \subset Aut P.
Proof. exact: subset_trans (morphpre_sub rho 1) sAP. Qed.

Lemma quotient_kernel_fixes a (aK : a \in 'ker rho) : {in Z, a =1 id}.
Proof. exact: fixesZ (subsetP (morphpre_sub rho 1) a aK). Qed.

Lemma quotient_kernel_displacement a (aK : a \in 'ker rho) x (xP : x \in P) :
  x^-1 * a x \in Z.
Proof.
have aA := subsetP (morphpre_sub rho 1) a aK.
have nx : x \in 'N(Z) := subsetP (normal_norm nZP) x xP.
have nax : a x \in 'N(Z) := subsetP (normal_norm nZP) _
  (Aut_closed (subsetP sAP a aA) xP).
apply: coset_equal_displacement nx nax _.
by rewrite -(rho_action aA xP) (mker aK) perm1.
Qed.

Definition quotient_kernel_delta :
    {morphism 'ker rho >-> {dffun forall q : [subg P / Z], gT}} :=
  @delta_morphism gT P Z ('ker rho)%G (normal_sub nZP) cZP
    quotient_kernel_sub_aut quotient_kernel_fixes quotient_kernel_displacement.

Lemma quotient_kernel_deltaE a (aK : a \in 'ker rho) x (xP : x \in P) :
  quotient_kernel_delta a (Sub (coset Z x) (mem_quotient Z xP)) = x^-1 * a x.
Proof.
exact: (@delta_function_coset gT P Z ('ker rho)%G (normal_sub nZP) cZP
  quotient_kernel_sub_aut quotient_kernel_fixes quotient_kernel_displacement a aK x xP).
Qed.

Lemma quotient_kernel_delta_injective : 'injm quotient_kernel_delta.
Proof. exact: delta_embedding_injective. Qed.

Lemma quotient_kernel_delta_image :
  quotient_kernel_delta @* 'ker rho \subset
  pointwise_hom_group [the finGroupType of [subg P / Z]%type]
    (central_displacement_abelian (normal_sub nZP) cZP).
Proof. exact: delta_embedding_image. Qed.

Lemma quotient_kernel_delta_pgroup (pi : nat_pred) :
  pi.-group Z -> pi.-group ('ker rho).
Proof.
exact: (@delta_embedding_pgroup gT P Z ('ker rho)%G (normal_sub nZP) cZP
  quotient_kernel_sub_aut quotient_kernel_fixes quotient_kernel_displacement pi).
Qed.
End QuotientKernelDelta.
