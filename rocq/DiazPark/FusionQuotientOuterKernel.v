From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation
  FusionOuterAutomorphisms FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientAutomorphisms.
Import DPFusionQuotientConstruction DPFusionQuotientAutomorphisms DPFusionOuter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionQuotientOuterKernel.
Section OuterKernel.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable P : {group coset_of Z}.

Definition kernel_outer : {group coset_of (inner (preimage P))} :=
  ('ker (automorphism_morphism cZ P) / inner (preimage P))%G.

Theorem kernel_outer_normal : kernel_outer <| outer_group F (preimage P).
Proof. exact: morphim_normal (ker_normal (automorphism_morphism cZ P)). Qed.

Theorem kernel_outer_pgroup (pi : nat_pred) : pi.-group Z -> pi.-group kernel_outer.
Proof.
move=> piZ; apply: quotient_pgroup.
exact: (@automorphism_kernel_pgroup S F Z cZ P pi piZ).
Qed.

Theorem kernel_outer_member (a : {perm S}) :
  a \in 'ker (automorphism_morphism cZ P) ->
  coset (inner (preimage P)) a \in kernel_outer.
Proof. exact: mem_quotient. Qed.

Theorem inner_automorphism_image :
  automorphism_morphism cZ P @* inner (preimage P) = inner P.
Proof.
apply/setP=> b; apply/idP/idP.
- move=> /morphimP[a _ /morphimP[s Ns Ps ->] ->].
  change (is_true (automorphism cZ P (conj_aut (preimage P) s) \in inner P)).
  rewrite automorphism_conjugation //.
  have Pqs : coset Z s \in P by move: Ps; rewrite (preimage_mem cZ).
  apply/morphimP; exists (coset Z s)=> //; exact: subsetP (normG P) _ Pqs.
- move=> /morphimP[s Ns Ps ->].
  pose r := fingroup.repr s.
  have Pr : r \in preimage P := repr_mem cZ Ps.
  have Nr := subsetP (normG (preimage P)) r Pr.
  have Ir : conj_aut (preimage P) r \in inner (preimage P).
    apply/morphimP; by exists r.
  have Ar := subsetP (inner_sub F (preimage P)) _ Ir.
  apply/morphimP; exists (conj_aut (preimage P) r)=> //.
  change (conj_aut P s = automorphism cZ P (conj_aut (preimage P) r)).
  by rewrite automorphism_conjugation // /r coset_reprK.
Qed.
End OuterKernel.
End DPFusionQuotientOuterKernel.

Print Assumptions DPFusionQuotientOuterKernel.kernel_outer_normal.
Print Assumptions DPFusionQuotientOuterKernel.kernel_outer_pgroup.
Print Assumptions DPFusionQuotientOuterKernel.inner_automorphism_image.
