From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category ModuleInfrastructure FusionMaps FusionSystems
  FusionOrbit FusionSaturation FusionOuterAutomorphisms FusionOuterOrbit FusionOuterAction
  FusionOuterEndomorphisms FusionMackeyShape MackeyStructures MackeyPair
  MackeyFusionBridge MackeyGroupActionOuter FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientAutomorphisms FusionQuotientOuterKernel FusionMackeyQuotientKernel.
Import DPFusionOrbit DPFusionOuter DPFusionOuterOrbit DPFusionQuotientConstruction
  DPFusionQuotientAutomorphisms DPFusionQuotientOuterKernel DPMackeyFusion.
Import GRing.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionMackeyQuotientKernelField.
Section FieldKernel.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable K : fieldType.
Variable M : mackey_pair K (orbit_category F).
Hypothesis hM : inclusion_mackey_formula M.
Let full := full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Variable p : nat.
Hypothesis charp : p \in [pchar K].
Hypothesis pZ : p.-group Z.

Theorem minimal_kernel_trivial (L : {group coset_of Z})
    (hQL : DPFusionSystem.conjugate F Q (preimage L)) a
    (aK : a \in 'ker (automorphism_morphism cZ L))
    (x : pair_value M (preimage L)) :
  pair_push M (aut_orbit F (preimage L) a) x = x.
Proof.
have aA := subsetP (morphpre_sub (automorphism_morphism cZ L) 1%G) a aK.
pose g : [subg outer_group F (preimage L)] := Subg (mem_quotient (inner (preimage L)) aA).
have hg : val g \in kernel_outer cZ L := kernel_outer_member aK.
have h := @DPMackeyOuterAction.conjugate_outer_normal_p_trivial S F K full
  (preimage L) Q leastQ simple hQL p charp (kernel_outer cZ L)
  (kernel_outer_normal cZ L) (kernel_outer_pgroup cZ L pZ) g hg x.
change (pair_push M (DPFusionOuterAction.outer_orbit F (val g)) x = x) in h.
by rewrite /g /= DPFusionOuterAction.outer_orbit_coset in h.
Qed.

Hypothesis sZQ : Z \subset Q.

Theorem kernel_push_trivial (P : {group coset_of Z}) a
    (aK : a \in 'ker (automorphism_morphism cZ P))
    (x : pair_value M (preimage P)) :
  pair_push M (aut_orbit F (preimage P) a) x = x.
Proof.
exact: (@DPFusionMackeyQuotientKernel.kernel_push_trivial S F Z cZ K M hM simple
  Q leastQ sZQ minimal_kernel_trivial P a aK x).
Qed.

Theorem kernel_pull_trivial (P : {group coset_of Z}) a
    (aK : a \in 'ker (automorphism_morphism cZ P))
    (x : pair_value M (preimage P)) :
  pair_pull M (aut_orbit F (preimage P) a) x = x.
Proof.
exact: (@DPFusionMackeyQuotientKernel.kernel_pull_trivial S F Z cZ K M hM simple
  Q leastQ sZQ minimal_kernel_trivial P a aK x).
Qed.
End FieldKernel.
End DPFusionMackeyQuotientKernelField.

Print Assumptions DPFusionMackeyQuotientKernelField.kernel_push_trivial.
Print Assumptions DPFusionMackeyQuotientKernelField.kernel_pull_trivial.
