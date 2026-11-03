From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFibration FusionMaps FusionSystems FusionOrbit
  FusionConjugacy FusionOrbitRanks FusionCentralizerCover FusionCentralizerCoverProjection.
Import DPFusion DPFusionOrbit DPFusionCentralizerCover DPFusionCentralizerCoverProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverCartesian.
Section Factorization.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Local Notation Ob := (cover_object F p).
Variables X Y Z : Ob.
Variable phi : DPFusionSystem.arrow F (carrier X) (carrier Y).
Hypothesis onto : DPFusion.image (val phi) = carrier Y.
Hypothesis hphi : raw_condition phi.
Variable h : cover_hom X Z.
Variable eta : DPFusion.map (elementary Z) (elementary Y).
Hypothesis heta : DPFusionSystem.allowed F eta.
Hypothesis overh : delta h = DPFusion.compose eta (raw_delta hphi).

Definition factor_raw : DPFusionSystem.arrow F (carrier Y) (carrier Z) :=
  Sub (DPFusion.compose (DPFusionConjugacy.onto_inverse onto) (val (repr (val h))))
    (DPFusionSystem.composition_closed (DPFusionConjugacy.onto_inverse_allowed onto (valP phi))
      (valP (repr (val h)))).

Lemma factor_raw_eta : {in elementary Z, forall z, val factor_raw (eta z) = z}.
Proof.
move=> z Ez; have Ey := DPFusion.map_into eta Ez.
have Yy := subsetP (elementary_sub Y) _ Ey.
have einv : DPFusionConjugacy.onto_inverse onto (eta z) = raw_delta hphi (eta z).
  apply: (DPFusion.map_injective (f := val phi) (DPFusion.map_into (DPFusionConjugacy.onto_inverse onto) Yy) (subsetP (elementary_sub X) _ (DPFusion.map_into (raw_delta hphi) Ey))).
  by rewrite DPFusionConjugacy.onto_inverse_cancel_right // raw_deltaE.
change (DPFusion.compose (DPFusionConjugacy.onto_inverse onto) (val (repr (val h))) (eta z) = z).
rewrite DPFusion.compose_in // einv.
have he := congr1 (fun a : DPFusion.map (elementary Z) (elementary X) => a z) overh.
rewrite DPFusion.compose_in // in he.
rewrite -he /delta. exact: (raw_deltaE (valP h) Ez).
Qed.

Lemma factor_condition : raw_condition factor_raw.
Proof.
apply/subsetP=> z Ez; apply/morphimP; exists (eta z).
- exact: subsetP (elementary_sub Y) _ (DPFusion.map_into eta Ez).
- exact (DPFusion.map_into eta Ez).
- exact: esym (factor_raw_eta Ez).
Qed.

Definition factor : cover_hom Y Z := cover_class factor_condition.
Lemma factor_delta : delta factor = eta.
Proof.
rewrite /factor delta_class; apply/esym/raw_delta_unique.
exact: factor_raw_eta.
Qed.

Lemma factor_composite : cover_compose (cover_class hphi) factor = h.
Proof.
apply: val_inj; change (orbit_compose (orbit_class phi) (orbit_class factor_raw) = val h).
rewrite orbit_compose_class.
have e : DPFusionSystem.arrow_compose phi factor_raw = repr (val h).
  apply: DPFusionSystem.arrow_ext=> x Xx.
  change (DPFusion.compose (val phi)
    (DPFusion.compose (DPFusionConjugacy.onto_inverse onto) (val (repr (val h)))) x =
    val (repr (val h)) x).
  by rewrite !DPFusion.compose_in ?DPFusion.map_into //
    DPFusionConjugacy.onto_inverse_cancel.
rewrite e; exact: reprK.
Qed.

Lemma factor_unique (k : cover_hom Y Z) :
  cover_compose (cover_class hphi) k = h -> k = factor.
Proof.
move=> hk; apply: val_inj.
have e : orbit_compose (orbit_class phi) (val k) =
    orbit_compose (orbit_class phi) (val factor).
  exact (congr1 val (eq_trans hk (esym factor_composite))).
pose iso := DPFusionRanks.raw_onto_iso onto.
have ei : orbit_compose (iso_inv iso) (orbit_class phi) = orbit_identity F (carrier Y).
  exact: iso_inv_hom iso.
have he := congr1 (fun a : orbit_hom F (carrier X) (carrier Z) =>
  orbit_compose (iso_inv iso) a) e.
change (Category.compose (iso_inv iso) (Category.compose (iso_hom iso) (val k)) =
  Category.compose (iso_inv iso) (Category.compose (iso_hom iso) (val factor))) in he.
rewrite -!Category.compose_assoc (iso_inv_hom iso) !Category.compose_id_left in he.
exact he.
Qed.
End Factorization.

Section Cartesian.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Variables X Y : centralized_object F p.
Variable phi : DPFusionSystem.arrow F (carrier (val X)) (carrier (val Y)).
Hypothesis onto : DPFusion.image (val phi) = carrier (val Y).
Hypothesis hphi : raw_condition phi.

Theorem onto_cover_cocartesian :
  @cocartesian (centralized_category F p) (opposite (elementary_category F p))
    (projection F p) X Y (cover_class hphi).
Proof.
move=> Z h beta he.
have he0 := congr1 val he.
change (DPFusion.compose (val beta) (delta (cover_class hphi)) = delta h) in he0.
rewrite delta_class in he0.
pose k := @factor S F p (val X) (val Y) (val Z) phi onto hphi h (val beta) (esym he0).
exists k; split.
- split.
  + apply: val_inj; exact: factor_delta.
  + exact: factor_composite.
- move=> j [_ hj]; exact (esym (@factor_unique S F p (val X) (val Y) (val Z) phi onto hphi h (val beta) (esym he0) j hj)).
Qed.
End Cartesian.
End DPFusionCentralizerCoverCartesian.











