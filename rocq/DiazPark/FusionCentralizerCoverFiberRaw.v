From mathcomp Require Import all_ssreflect all_fingroup center abelian pgroup generic_quotient.
From DiazPark Require Import Category CategoryFibration FusionMaps FusionSystems FusionSaturation
  FusionOrbit FusionCentralizerMaps FusionCentralizer FusionCentralizerAmbient FusionCentralizerCentric
  FusionSubsystemOrbit FusionSubsystemFaithful FusionCentralizerCover FusionCentralizerCoverProjection
  FusionCentralizerCoverFibration FusionCentralizerCoverFiberObjects.
Import DPFusion DPFusionOrbit DPFusionSubgroup DPFusionSubsystem DPFusionCentralizerCover
  DPFusionCentralizerCoverProjection DPFusionCentralizerCoverFiberObjects.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverFiberRaw.
Section Maps.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation T := [subg 'C(E)]%type.
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation hH := (@DPFusionCentralizerAmbient.lift_allowed S F E).
Local Notation co := (@cover_of_local S F p pS sat B).
Local Notation fo := (@fiber_of_local S F p pS sat B).
Local Notation Fib := (fiber_category (functor_op (projection F p)) B).

Lemma lift_fixes (P Q : centric_object CF) (f : DPFusionSystem.arrow CF (val P) (val Q)) :
  {in E, DPFusionSubgroup.lift (val f) =1 id}.
Proof.
have /DPFusionCentralizer.allowedP[fh [hfh [he hf]]] := valP f.
move=> z Ez.
have Pz := subsetP (@ambient_contains S F p B P) z Ez.
have Pzg := ambient_repr Pz.
have h := he (subg 'C(E) z) Pzg.
rewrite (ambient_subgK Pz) hf // in h.
have hz := DPFusionSubgroup.liftE (val f) Pzg.
rewrite (ambient_subgK Pz) in hz; exact (eq_trans hz (esym h)).
Qed.

Lemma lower_allowed_of_fixes (P Q : centric_object CF)
    (f : DPFusion.map (ambient (val P)) (ambient (val Q))) :
  DPFusionSystem.allowed F f -> {in E, f =1 id} ->
  DPFusionSystem.allowed CF (DPFusionSubgroup.lower f).
Proof.
move=> hf hfix.
have eP := DPFusionCentralizerCentric.joint_eq_of_centric (elementary_abelian B) (valP P).
have eQ := DPFusionCentralizerCentric.joint_eq_of_centric (elementary_abelian B) (valP Q).
apply/DPFusionCentralizer.allowedP.
exists (DPFusionSubgroup.reindex (esym eP) (esym eQ) f); split.
- exact: DPFusionSubgroup.reindex_allowed hf.
- split.
  + move=> x Px; rewrite DPFusionSubgroup.reindexE DPFusionSubgroup.lowerE //.
  + move=> z Ez; rewrite DPFusionSubgroup.reindexE; exact: hfix Ez.
Qed.

Lemma lift_lower (P Q : {group T}) (f : DPFusion.map (ambient P) (ambient Q)) :
  DPFusionSubgroup.lift (DPFusionSubgroup.lower f) = f.
Proof.
apply: DPFusion.map_ext=> x Px.
rewrite -(ambient_subgK Px) DPFusionSubgroup.liftE ?ambient_repr //.
by rewrite DPFusionSubgroup.lowerE ?ambient_repr // (ambient_subgK Px).
Qed.


End Maps.
End DPFusionCentralizerCoverFiberRaw.

