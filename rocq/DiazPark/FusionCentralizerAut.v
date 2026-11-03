From mathcomp Require Import all_ssreflect all_fingroup pgroup.
From DiazPark Require Import FusionMaps FusionSystems FusionSaturation FusionAutomorphisms
  FusionCentralizerMaps FusionCentralizer.
Import DPFusion DPFusionSubgroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.

Module DPFusionCentralizerAut.

Section JointAutomorphisms.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable E : {group S}.
Local Notation C := 'C(E)%G.
Local Notation T := [subg C]%type.
Local Notation J P := (DPFusionCentralizer.joint (E := E) P).

(** Actual allowed automorphisms of P E preserving P and fixing E pointwise. *)
Definition K_set (P : {group T}) :=
  [set a in DPFusionSaturation.aut_group F (J P) |
    [forall x in ambient P, a x \in ambient P] && [forall e in E, a e == e]].

Lemma K_group_set (P : {group T}) : group_set (K_set P).
Proof.
apply/group_setP; split.
- apply/setIdP; split; first exact: group1.
  apply/andP; split; apply/forall_inP=> x Px; by rewrite perm1.
- move=> a b /setIdP[Fa /andP[/forall_inP ha /forall_inP ea]]
    /setIdP[Fb /andP[/forall_inP hb /forall_inP eb]].
  apply/setIdP; split; first exact: groupM Fa Fb.
  apply/andP; split; apply/forall_inP=> x Px; rewrite permM.
  + exact: hb _ (ha _ Px).
  + by rewrite (eqP (ea x Px)) (eqP (eb x Px)).
Qed.

Definition K (P : {group T}) : {group {perm S}} := group (K_group_set P).

Lemma K_sub (P : {group T}) : K P \subset DPFusionSaturation.aut_group F (J P).
Proof. by apply/subsetP=> a /setIdP[Fa _]. Qed.

Lemma K_preserves (P : {group T}) (a : {perm S}) :
  a \in K P -> {in ambient P, forall x, a x \in ambient P}.
Proof. by move=> /setIdP[_ /andP[/forall_inP h _]]. Qed.

Lemma K_preserves_iff (P : {group T}) (a : {perm S}) :
  a \in K P -> forall x, (a x \in ambient P) = (x \in ambient P).
Proof.
move=> Ka x; apply/idP/idP; last by move=> Px; exact: (@K_preserves P a Ka x Px).
move=> Pax.
have Kai : a^-1 \in K P by rewrite groupV.
have h := @K_preserves P a^-1 Kai (a x) Pax.
by rewrite permK in h.
Qed.

Lemma K_fixes (P : {group T}) (a : {perm S}) :
  a \in K P -> {in E, a =1 id}.
Proof.
move=> /setIdP[_ /andP[_ /forall_inP h]] e Ee.
exact: eqP (h e Ee).
Qed.

End JointAutomorphisms.

Arguments K {S} F E P.
Arguments K_sub {S} F E P.
Arguments K_preserves {S F E P a} _ {x} _.
Arguments K_preserves_iff {S F E P a} _ x.
Arguments K_fixes {S F E P a} _ {x} _.

End DPFusionCentralizerAut.
