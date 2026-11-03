From mathcomp Require Import all_ssreflect all_fingroup center pgroup sylow.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionConjugacy FusionAutomorphisms FusionCentricCriterion
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientNormalization
  FusionQuotientAutomorphisms FusionQuotientCentric.
Import DPFusion DPFusionQuotientConstruction DPFusionQuotientAutomorphisms
  DPFusionQuotientCentric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientCentricTransport.
Section InnerTransport.
Variable S : finGroupType.
Variables P Q : {group S}.
Variable f : DPFusion.map P Q.

Lemma aut_transport_inner_reflect (a : {perm S}) :
  a \in Aut P ->
  DPFusionAutomorphisms.aut_transport f a \in
    conj_aut (DPFusion.image f) @* DPFusion.image f ->
  a \in conj_aut P @* P.
Proof.
move=> aAut /morphimP[y Ny Iy eb].
have /morphimP[x Px _ ex] := Iy.
have Nx : x \in 'N(P) := subsetP (normG P) x Px.
have eqa : a = conj_aut P x.
  apply: (eq_Aut aAut (Aut_aut _ _))=> z Pz.
  rewrite norm_conj_autE //.
  apply: (DPFusion.map_injective (f := f) (Aut_closed aAut Pz) (groupJ Pz Px)).
  rewrite -(DPFusionAutomorphisms.aut_transportE f aAut Pz) eb norm_conj_autE
    ?DPFusion.image_mem //.
  rewrite ex.
  exact: esym (morphJ (DPFusion.map_morphism f) Pz Px).
apply/morphimP; by exists x.
Qed.

End InnerTransport.

Section KernelTransport.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.

Lemma kernel_transport (P Q : {group coset_of Z})
    (f : DPFusion.map (preimage P) (preimage Q)) (a : {perm S}) :
  DPFusionSystem.allowed F f -> DPFusion.image f = preimage Q ->
  a \in 'ker (automorphism_morphism cZ P) ->
  DPFusionAutomorphisms.aut_transport f a \in 'ker (automorphism_morphism cZ Q).
Proof.
move=> Ff onto aK.
have [aA ha] := proj1 (kernel_iff cZ P a) aK.
have aAut := subsetP (DPFusionSaturation.aut_group_sub F (preimage P)) a aA.
have bA := DPFusionAutomorphisms.aut_transport_allowed Ff aA.
rewrite onto in bA.
apply: (proj2 (kernel_iff cZ Q _)); split=> // y Qy.
have Iy : y \in DPFusion.image f by rewrite onto.
have /morphimP[x Px _ ->] := Iy.
change (coset Z (DPFusionAutomorphisms.aut_transport f a (f x)) = coset Z (f x)).
rewrite DPFusionAutomorphisms.aut_transportE //.
have [b hb] := @exists_descended S F Z cZ P Q f Ff.
rewrite -(descendsE hb (Aut_closed aAut Px)) (ha x Px).
exact: (@descendsE S Z P Q f b hb x Px).
Qed.

Theorem centric_kernel_inner (P : {group coset_of Z}) (p : nat) :
  p.-group Z -> DPFusionSaturation.saturated F p ->
  DPFusionSystem.centric (system cZ) P ->
  'ker (automorphism_morphism cZ P) \subset conj_aut (preimage P) @* preimage P.
Proof.
move=> pZ sat hC.
have [Q [hPQ hN]] := DPFusionConjugacy.fully_normalized_conjugate_exists (system cZ) P.
have hCQ := centric_conjugate hPQ hC.
have /existsP[b /andP[/existsP[f /andP[Ff hf]] /eqP onto]] := hPQ.
have ontof := @lift_onto S F Z cZ P Q f b Ff hf onto.
apply/subsetP=> a aK.
have aA := subsetP (morphpre_sub (automorphism_morphism cZ P) 1) a aK.
have aAut := subsetP (DPFusionSaturation.aut_group_sub F (preimage P)) a aA.
have bk := kernel_transport Ff ontof aK.
have bi := subsetP (@normalized_kernel_inner S F Z cZ Q p pZ sat hN hCQ) _ bk.
apply: (@aut_transport_inner_reflect S (preimage P) (preimage Q) f a aAut).
by rewrite ontof.
Qed.

End KernelTransport.
End DPFusionQuotientCentricTransport.

Print Assumptions DPFusionQuotientCentricTransport.aut_transport_inner_reflect.
Print Assumptions DPFusionQuotientCentricTransport.kernel_transport.
Print Assumptions DPFusionQuotientCentricTransport.centric_kernel_inner.
