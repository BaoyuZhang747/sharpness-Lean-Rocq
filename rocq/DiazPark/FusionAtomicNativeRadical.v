From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionSystems FusionRadical FusionOuterAutomorphisms
  FusionAtomicFunctorPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionAtomicNativeRadical.
Section NativeRadical.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Variable Q : {group S}.
Local Notation G := (DPFusionOuter.outer_group F Q).
Local Notation GT := (DPFusionAtomicPreimages.outer_type F Q).

Definition native_pcore : {group GT} := (subg G @* 'O_p(G))%G.
Lemma native_pcore_pgroup : p.-group native_pcore.
Proof. exact: morphim_pgroup (pcore_pgroup p G). Qed.
Lemma native_pcore_normal : native_pcore <| [set: GT].
Proof.
have h := morphim_normal (subg G) (pcore_normal p G).
by rewrite im_subg in h.
Qed.
Lemma native_pcore_nontrivial :
  ~~ DPFusionRadical.radical F p Q -> native_pcore :!=: 1%G.
Proof.
move=> hn; apply/negP=> /eqP h.
have k := subgmK (pcore_sub p G).
change (sgval @* native_pcore = 'O_p(G)) in k.
rewrite h morphim1 in k.
move: hn; by rewrite /DPFusionRadical.radical -k eqxx.
Qed.
End NativeRadical.
End DPFusionAtomicNativeRadical.
