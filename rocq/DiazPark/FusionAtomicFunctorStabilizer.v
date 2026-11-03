From mathcomp Require Import all_ssreflect all_fingroup pgroup generic_quotient.
From DiazPark Require Import GroupActionOrbitRepresentatives Category FusionMaps FusionSystems FusionOrbit FusionOuterAutomorphisms
  FusionOuterAction FusionOuterCard FusionAtomicStabilizer FusionAtomicCentricStabilizer
  FusionAtomicFunctorPreimages FusionAtomicFunctorFixed.
Import DPFusion DPFusionOrbit DPFusionAtomicPreimages DPFusionAtomicFixed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionAtomicNativeStabilizer.
Section Native.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Q : {group S}.
Local Notation G0 := (DPFusionOuter.outer_group F Q).
Local Notation G := (outer_type F Q).

Definition action (P : {group S}) (g : G) (f : orbit_hom F Q P) :=
  orbit_compose (@outer_orbit S F Q g) f.
Lemma action_one (P : {group S}) (f : orbit_hom F Q P) : action 1 f = f.
Proof. exact: DPFusionOuterAction.action_one. Qed.
Lemma action_mul (P : {group S}) (g h : G) (f : orbit_hom F Q P) :
  action (g*h) f = action g (action h f).
Proof. exact: DPFusionOuterAction.action_mul (valP g) (valP h). Qed.

Definition stabilizer (P : {group S}) (f : orbit_hom F Q P) : {group G} :=
  (subg G0 @* DPFusionOuterAction.stabilizer f)%G.
Lemma stabilizer_mem (P : {group S}) (f : orbit_hom F Q P) (g : G) :
  g \in stabilizer f <-> action g f = f.
Proof.
split.
- move/morphimP=> [a Ga /setIdP[_ /eqP ha] eg].
  have ev : val g = a by rewrite eg subgK.
  change (DPFusionOuterAction.action (val g) f = f); by rewrite ev.
- move=> hg; apply/morphimP; exists (val g); first exact: valP.
  + apply/setIdP; split; first exact: valP.
    apply/eqP; exact hg.
  + apply: val_inj; exact (esym (@subgK _ G0 (val g) (valP g))).
Qed.

Lemma stabilizer_isog (P : {group S}) (f : orbit_hom F Q P) :
  DPFusionOuterAction.stabilizer f \isog stabilizer f.
Proof. exact: sub_isog (DPFusionOuterAction.stabilizer_sub f) (injm_subg _). Qed.

Lemma stabilizer_pgroup (p : nat) (P : {group S}) (f : orbit_hom F Q P) :
  p.-group P -> p.-group (stabilizer f).
Proof.
move=> pP; apply: morphim_pgroup.
move: f; apply: quotW=> f; exact: DPFusionAtomicStabilizer.stabilizer_pgroup pP.
Qed.

Lemma stabilizer_nontrivial (p : nat) (P : {group S}) (f : orbit_hom F Q P) :
  p.-group P -> DPFusionSystem.centric F Q ->
  (forall e : @isomorphism (orbit_category F) Q P, False) -> stabilizer f :!=: 1.
Proof.
move=> pP hc hn; rewrite -(isog_eq1 (stabilizer_isog f)).
move: f; apply: quotW=> f.
have [_ [_ h]] := DPFusionAtomicCentricStabilizer.atomic_stabilizer_theorem f pP hc.
exact: h hn.
Qed.

Lemma generic_stabilizer (P : {group S}) (f : orbit_hom F Q P) :
  @DPLeftAction.stabilizer G [the finType of orbit_hom F Q P] (@action P)
    (@action_one P) (@action_mul P) f = stabilizer f.
Proof.
apply: val_inj; apply/setP=> g.
apply/DPLeftAction.stabilizerP/idP.
- move=> hg; exact: (proj2 (stabilizer_mem f g) hg).
- move=> hg; exact: (proj1 (stabilizer_mem f g) hg).
Qed.

Lemma outer_orbit_surjective (f : orbit_hom F Q Q) :
  exists g : G, @outer_orbit S F Q g = f.
Proof.
have [g [Gg hg]] := DPFusionOuterCard.outer_orbit_surjective f.
exists (Sub g Gg); exact hg.
Qed.

End Native.
End DPFusionAtomicNativeStabilizer.






