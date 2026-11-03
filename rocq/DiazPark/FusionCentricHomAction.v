From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionSaturation
  FusionOrbit FusionOuterOrbit FusionCentricBasics FusionCentricNormalizerExtension
  FusionCentricRigidity.
Import DPFusion DPFusionOrbit DPFusionOuterOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricHomAction.
Section Action.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P T N : {group S}.
Hypothesis sNN : N \subset 'N(P).
Local Notation nT := [subg N]%type.

Definition conjugation_orbit (n : nT) : orbit_hom F P P :=
  aut_orbit F P (conj_aut P (val n)).

Lemma conjugation_allowed (n : nT) :
  conj_aut P (val n) \in DPFusionSaturation.aut_group F P.
Proof.
apply: (subsetP (DPFusionSaturation.ambient_aut_sub F P)).
apply/morphimP; exists (val n)=> //; exact: subsetP sNN _ (valP n).
Qed.

Lemma conjugation_orbit_one : conjugation_orbit 1 = orbit_identity F P.
Proof. by rewrite /conjugation_orbit /= morph1 aut_orbit_one. Qed.

Lemma conjugation_orbit_mul (n m : nT) :
  conjugation_orbit (n*m) = orbit_compose (conjugation_orbit n) (conjugation_orbit m).
Proof.
rewrite /conjugation_orbit /= conj_aut_morphM ?(subsetP sNN _ (valP _)) //.
exact: aut_orbit_mul (conjugation_allowed n) (conjugation_allowed m).
Qed.

(** Precomposition by inverse conjugation is a genuine right action. *)
Definition hom_action (f : orbit_hom F P T) (n : nT) :=
  orbit_compose (conjugation_orbit n^-1) f.

Lemma hom_action_one f : hom_action f 1 = f.
Proof.
rewrite /hom_action invg1 conjugation_orbit_one.
exact: (@Category.compose_id_left (orbit_category F) P T f).
Qed.

Lemma hom_action_mul f : act_morph hom_action f.
Proof.
move=> n m; rewrite /hom_action invMg conjugation_orbit_mul.
exact: (@Category.compose_assoc (orbit_category F) P P P T _ _ f).
Qed.

Definition normalizer_action : {action nT &-> orbit_hom F P T} :=
  TotalAction hom_action_one hom_action_mul.

Lemma fixed_iff (beta : DPFusionSystem.arrow F P T) :
  orbit_class beta \in 'Fix_normalizer_action([set: nT]) <->
  forall n, n \in N -> exists t, t \in T /\
    {in P, forall x, (val beta) (x ^ n) = ((val beta) x) ^ t}.
Proof.
split.
- move/afixP=> hf n Nn.
  pose nn : nT := Sub n Nn.
  have hnn : nn^-1 \in [set: nT] by rewrite inE.
  have e := hf nn^-1 hnn.
  change (hom_action (orbit_class beta) nn^-1 = orbit_class beta) in e.
  rewrite /hom_action invgK /conjugation_orbit /aut_orbit orbit_compose_class in e.
  have [t [Tt ht]] := proj1 (orbit_class_eq_iff _ _) (esym e).
  exists t; split=> // x Px.
  have h := ht x Px.
  change (DPFusion.compose (aut_map F P (conj_aut P (val nn))) (val beta) x = ((val beta) x)^t) in h.
  rewrite DPFusion.compose_in // aut_mapE ?conjugation_allowed // in h.
  by rewrite norm_conj_autE ?(subsetP sNN _ Nn) // in h.
- move=> hf; apply/afixP=> n _.
  change (hom_action (orbit_class beta) n = orbit_class beta).
  rewrite /hom_action /conjugation_orbit /aut_orbit orbit_compose_class.
  symmetry; apply/orbit_class_eq/exists_inP.
  have [t [Tt ht]] := hf (val n^-1) (valP n^-1).
  exists t=> //; apply/forall_inP=> x Px; apply/eqP.
  change (DPFusion.compose (aut_map F P (conj_aut P (val n^-1))) (val beta) x = ((val beta) x)^t).
  rewrite DPFusion.compose_in // aut_mapE ?conjugation_allowed //.
  rewrite norm_conj_autE ?(subsetP sNN _ (valP n^-1)) //.
  exact: ht x Px.
Qed.

End Action.
End DPFusionCentricHomAction.


