From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape TraceMackeySurvivors MackeyPair.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionMackey DPMackeyTrace.
Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerAction.
Section QuotientArrows.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable H : {group S}.

Definition normalizer_class t (ht : t \in 'N(H)) : DPFusionOrbit.orbit_hom F H H :=
  DPFusionOrbit.orbit_class (normalizer_arrow F ht).

Lemma normalizer_class_proof_irrel t (ht hu : t \in 'N(H)) :
    normalizer_class ht = normalizer_class hu.
Proof.
rewrite /normalizer_class.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Hx.
by rewrite !normalizer_arrow_value.
Qed.

Lemma normalizer_class_mul a b (ha : a \in 'N(H)) (hb : b \in 'N(H)) :
    @Category.compose (DPFusionOrbit.orbit_category F) H H H
      (normalizer_class ha) (normalizer_class hb) =
    normalizer_class (groupM ha hb).
Proof.
cbn [Category.compose DPFusionOrbit.orbit_category]; rewrite /normalizer_class.
rewrite DPFusionOrbit.orbit_compose_class.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Hx.
change (DPFusion.compose (val (normalizer_arrow F ha)) (val (normalizer_arrow F hb)) x =
  (val (normalizer_arrow F (groupM ha hb))) x).
rewrite DPFusion.compose_in // !normalizer_arrow_value //.
- by rewrite conjgM.
- by rewrite memJ_norm.
Qed.

Lemma normalizer_class_inner h (hh : h \in H) (hn : h \in 'N(H)) :
    normalizer_class hn = DPFusionOrbit.orbit_identity F H.
Proof.
apply/DPFusionOrbit.orbit_class_eq; apply/exists_inP; exists (h^-1)%g.
- by rewrite groupV.
- apply/forall_inP=> x Hx; apply/eqP.
  change (DPFusion.identity H x = ((val (normalizer_arrow F hn)) x ^ h^-1)%g).
  by rewrite DPFusion.identity_in // normalizer_arrow_value // conjgK.
Qed.

Lemma normalizer_class_coset a b (ha : a \in 'N(H)) (hb : b \in 'N(H)) :
    coset H a = coset H b -> normalizer_class ha = normalizer_class hb.
Proof.
move=> hab.
have hset := congr1 (fun q : coset_of H => (q : {set S})) hab.
rewrite !val_coset // in hset.
have hamem : a \in H :* b by rewrite -hset rcoset_refl.
have /rcosetP[h Hh eh] := hamem.
have Hnh : h \in 'N(H) := subsetP (normG H) h Hh.
subst a.
rewrite (normalizer_class_proof_irrel ha (groupM Hnh hb)).
rewrite -normalizer_class_mul (normalizer_class_inner Hh Hnh).
exact (@Category.compose_id_left (DPFusionOrbit.orbit_category F) H H (normalizer_class hb)).
Qed.

Definition quotient_class (q : coset_of H) : DPFusionOrbit.orbit_hom F H H :=
  normalizer_class (repr_coset_norm q).

Lemma quotient_class_coset t (ht : t \in 'N(H)) :
    quotient_class (coset H t) = normalizer_class ht.
Proof. apply: normalizer_class_coset; exact: coset_reprK. Qed.

Lemma quotient_class_mul (q r : coset_of H) :
    @Category.compose (DPFusionOrbit.orbit_category F) H H H
      (quotient_class q) (quotient_class r) = quotient_class (q * r)%g.
Proof.
rewrite /quotient_class normalizer_class_mul.
apply: normalizer_class_coset.
rewrite morphM ?repr_coset_norm // !coset_reprK.
change ((coset H (fingroup.repr q) * coset H (fingroup.repr r))%g = (q * r)%g).
by rewrite !coset_reprK.
Qed.

Lemma quotient_class_one : quotient_class (1%g : coset_of H) = DPFusionOrbit.orbit_identity F H.
Proof.
apply: normalizer_class_inner.
by rewrite repr_coset1 group1.
Qed.

End QuotientArrows.

Section ModuleAction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).
Variable H : {group S}.

Definition quotient_action (v : pair_value M H) (q : coset_of H) :=
  pair_push M (quotient_class F q) v.

Lemma quotient_action_mul v a b :
    quotient_action (quotient_action v a) b = quotient_action v (a * b)%g.
Proof. by rewrite /quotient_action -pair_push_comp quotient_class_mul. Qed.

Lemma quotient_action_one v : quotient_action v (1%g : coset_of H) = v.
Proof. by rewrite /quotient_action quotient_class_one pair_push_id. Qed.

End ModuleAction.
End DPNormalizerAction.

Print Assumptions DPNormalizerAction.normalizer_class_coset.
Print Assumptions DPNormalizerAction.quotient_class_mul.
Print Assumptions DPNormalizerAction.quotient_action_mul.
