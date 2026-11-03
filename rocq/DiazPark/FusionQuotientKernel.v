From mathcomp Require Import all_ssreflect all_fingroup center pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientNormalization
  FusionQuotientAutomorphisms GroupDeltaEmbedding GroupQuotientDelta.
Import DPFusion DPFusionQuotientConstruction DPFusionQuotientAutomorphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientKernel.
Section Kernel.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable P : {group coset_of Z}.
Let A := DPFusionSaturation.aut_group F (preimage P).
Let rho := automorphism_morphism cZ P.

Lemma centralizes_preimage : Z \subset 'C(preimage P).
Proof.
have cZT : Z \subset 'C([set: S]).
  exact: subset_trans (DPFusionQuotient.central_sub_center cZ) (subsetIr _ _).
exact: centsS (subsetT (preimage P)) cZT.
Qed.

Lemma kernel_normal : 'ker rho <| A.
Proof. exact: ker_normal. Qed.

(** The actual displayed map from the manuscript, specialized to the
    constructed quotient fusion system and its actual automorphism map. *)
Definition kernel_delta :
    {morphism 'ker rho >-> {dffun forall q : [subg preimage P / Z], S}} :=
  @quotient_kernel_delta S (preimage P) Z A
    (normal_cosetpre P) centralizes_preimage
    (DPFusionSaturation.aut_group_sub F (preimage P))
    (fun a aA => @automorphism_fixes_kernel S F Z cZ P a aA)
    rho (fun a aA x xP => @automorphismE S F Z cZ P a aA x xP).

Lemma kernel_deltaE a (aK : a \in 'ker rho) x (xP : x \in preimage P) :
  kernel_delta a (Sub (coset Z x) (mem_quotient Z xP)) = x^-1 * a x.
Proof. exact: quotient_kernel_deltaE. Qed.

Lemma kernel_delta_injective : 'injm kernel_delta.
Proof. exact: quotient_kernel_delta_injective. Qed.

Lemma kernel_delta_image :
  kernel_delta @* 'ker rho \subset
  pointwise_hom_group [the finGroupType of [subg preimage P / Z]%type]
    (central_displacement_abelian (kernel_sub_preimage P) centralizes_preimage).
Proof. exact: quotient_kernel_delta_image. Qed.

Lemma kernel_pgroup_via_delta (pi : nat_pred) :
  pi.-group Z -> pi.-group ('ker rho).
Proof.
exact: (@quotient_kernel_delta_pgroup S (preimage P) Z A
  (normal_cosetpre P) centralizes_preimage
  (DPFusionSaturation.aut_group_sub F (preimage P))
  (fun a aA => @automorphism_fixes_kernel S F Z cZ P a aA)
  rho (fun a aA x xP => @automorphismE S F Z cZ P a aA x xP) pi).
Qed.

Lemma normalizer_quotient : ('N(preimage P) / Z)%G = 'N(P)%G.
Proof.
by rewrite -(@DPFusionQuotientNormalization.normalizer_preimage S F Z cZ P)
  preimage_quotient.
Qed.

End Kernel.
End DPFusionQuotientKernel.
