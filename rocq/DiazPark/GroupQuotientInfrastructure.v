From mathcomp Require Import all_ssreflect fingroup perm morphism automorphism.
From mathcomp Require Import quotient cyclic pgroup sylow.
From DiazPark Require Import GroupInfrastructure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

(** Full preimages, rather than arbitrary representatives of quotient
    subgroups.  Normality hypotheses ensure that MathComp's quotient
    convention agrees with the ordinary subgroup quotient. *)
Section FullPreimages.
Variable gT : finGroupType.
Variables S Z : {group gT}.
Hypothesis nZS : Z <| S.

Definition quotient_full_preimage (Q : {group coset_of Z}) : {group gT} :=
  (coset Z @*^-1 Q)%G.

Lemma quotient_full_preimage_contains Q : Z \subset quotient_full_preimage Q.
Proof. exact: sub_cosetpre. Qed.

Lemma quotient_full_preimage_normal Q : Z <| quotient_full_preimage Q.
Proof. exact: normal_cosetpre. Qed.

Lemma quotient_full_preimage_sub (Q : {group coset_of Z}) :
  Q \subset S / Z -> quotient_full_preimage Q \subset S.
Proof. by rewrite /quotient_full_preimage sub_cosetpre_quo. Qed.

Lemma quotient_full_preimage_quotient Q : quotient_full_preimage Q / Z = Q.
Proof. exact: cosetpreK. Qed.

Lemma quotient_full_preimage_card Q :
  #|quotient_full_preimage Q| = (#|Z| * #|Q|)%N.
Proof. exact: card_cosetpre. Qed.

Variable P : {group gT}.
Hypotheses (sZP : Z \subset P) (sPS : P \subset S).

Lemma quotient_normalizer_contains_kernel : Z \subset 'N_S(P).
Proof.
apply/subsetP=> z Zz; apply/setIP; split.
- exact: subsetP (normal_sub nZS) z Zz.
- exact: subsetP (normG P) z (subsetP sZP z Zz).
Qed.

Lemma quotient_normalizer_kernel_normal : Z <| 'N_S(P).
Proof.
exact: normalS quotient_normalizer_contains_kernel (subsetIl S 'N(P)) nZS.
Qed.

Lemma quotient_normalizer_preimage :
  coset Z @*^-1 'N_(S / Z)(P / Z) = 'N_S(P).
Proof.
have nZP : Z <| P := normalS sZP sPS nZS.
rewrite -(quotient_subnormG S nZP).
exact: quotientGK quotient_normalizer_kernel_normal.
Qed.

Lemma quotient_normalizer_card :
  #|'N_S(P)| = (#|Z| * #|'N_(S / Z)(P / Z)|)%N.
Proof. by rewrite -quotient_normalizer_preimage card_cosetpre. Qed.

End FullPreimages.

(** Equality of images modulo the kernel lifts to actual equality of
    subgroups when the image contains that kernel. *)
Section QuotientImage.
Variable gT : finGroupType.
Variables P Q Z : {group gT}.
Variable f : {morphism P >-> gT}.
Hypothesis sZP : Z \subset P.
Hypothesis fixesZ : {in Z, f =1 id}.

Lemma fixed_subgroup_in_morphism_image : Z \subset f @* P.
Proof.
apply/subsetP=> z Zz; have Pz := subsetP sZP z Zz.
apply/morphimP; exists z=> //.
by rewrite fixesZ.
Qed.

Lemma morphism_image_eq_of_quotient_eq :
  Z <| Q -> f @* P \subset Q -> (f @* P) / Z = Q / Z -> f @* P = Q.
Proof.
move=> nZQ sIQ eqIQ.
have nZI : Z <| f @* P := normalS fixed_subgroup_in_morphism_image sIQ nZQ.
exact: quotient_inj nZI nZQ eqIQ.
Qed.

End QuotientImage.

(** This bridge is stated with membership in the normalizer because
    coset Z is a morphism on N(Z), not on the whole ambient group. *)
Section CosetDisplacement.
Variable gT : finGroupType.
Variable Z : {group gT}.

Lemma coset_equal_displacement x y :
  x \in 'N(Z) -> y \in 'N(Z) -> coset Z y = coset Z x -> x^-1 * y \in Z.
Proof.
move=> nx ny eqxy.
have nxV : x^-1 \in 'N(Z) by rewrite groupV.
apply: coset_idr.
- exact: groupM nxV ny.
- rewrite (morphM (coset Z) nxV ny) (morphV (coset Z) nx).
  exact: (eq_trans (congr1 (fun c => (coset Z x)^-1 * c) eqxy)
    (mulVg (coset Z x))).
Qed.

End CosetDisplacement.

(** The kernel of a genuine induced quotient action is a p-group.
    The map rho is an actual group morphism, and its action is required
    to be the quotient of the original action.  No p-kernel conclusion
    is assumed.  Centrality is not needed for this finite-group lemma. *)
Section QuotientAutomorphismKernel.
Variable gT : finGroupType.
Variables P Z : {group gT}.
Variable A : {group {perm gT}}.
Hypotheses (nZP : Z <| P) (sAP : A \subset Aut P).
Hypothesis fixesZ : forall a, a \in A -> {in Z, a =1 id}.
Variable rho : {morphism A >-> {perm (coset_of Z)}}.
Hypothesis rho_action :
  forall a, a \in A -> forall x, x \in P ->
    rho a (coset Z x) = coset Z (a x).

Lemma quotient_automorphism_kernel_pgroup (pi : nat_pred) :
  pi.-group Z -> pi.-group ('ker rho).
Proof.
move=> piZ.
have sKA : 'ker rho \subset A := morphpre_sub rho 1.
have sKP : 'ker rho \subset Aut P := subset_trans sKA sAP.
have fixK : forall a, a \in 'ker rho -> {in Z, a =1 id}.
  move=> a aK; exact: fixesZ (subsetP sKA a aK).
have dispK : forall a, a \in 'ker rho -> forall x, x \in P -> x^-1 * a x \in Z.
  move=> a aK x xP.
  have aA := subsetP sKA a aK.
  have aAut := subsetP sAP a aA.
  have nx : x \in 'N(Z) := subsetP (normal_norm nZP) x xP.
  have nax : a x \in 'N(Z) :=
    subsetP (normal_norm nZP) (a x) (Aut_closed aAut xP).
  apply: coset_equal_displacement nx nax _.
  by rewrite -(rho_action aA xP) (mker aK) perm1.
exact: (@automorphism_displacement_pgroup gT P Z ('ker rho)%G
  sKP (normal_sub nZP) fixK dispK pi piZ).
Qed.

Lemma quotient_automorphism_kernel_sub_sylow (p : nat) (U : {group {perm gT}}) :
  p.-group Z -> p.-Sylow(A) U -> 'ker rho \subset U.
Proof.
move=> pZ sylU.
exact: normal_pgroup_sub_sylow (ker_normal rho)
  (quotient_automorphism_kernel_pgroup pZ) sylU.
Qed.

End QuotientAutomorphismKernel.
