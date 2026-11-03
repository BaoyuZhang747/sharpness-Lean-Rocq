From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape FusionOrbitRanks MackeyPair MackeyPairSpanIso TraceNormalizerCosets.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionMackey DPFusionRanks.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPMackeyRepresentatives.
Section Geometry.
Variable S : finGroupType.
Variable F : system S.
Variables H K : {group S}.
Variables h t k : S.
Hypotheses (hH : h \in H) (kK : k \in K).

Lemma translated_apex :
    (inclusion_apex H K (h*t*k)) :^ h = inclusion_apex H K t.
Proof.
rewrite /inclusion_apex conjIg (normP (subsetP (normG H) _ hH)).
rewrite -conjsgM !invgM -!mulgA mulVg mulg1 conjsgM.
have hk : k^-1 \in 'N(K) by rewrite groupV; exact: subsetP (normG K) _ kK.
by rewrite (normP hk).
Qed.

Lemma translated_sub : inclusion_apex H K (h*t*k) :^ h \subset inclusion_apex H K t.
Proof. by rewrite translated_apex. Qed.

Definition translated_arrow : arrow F (inclusion_apex H K (h*t*k)) (inclusion_apex H K t) :=
  Sub (conjugation translated_sub)
    (conjugation_closed F translated_sub).

Lemma translated_rank : #|inclusion_apex H K (h*t*k)| = #|inclusion_apex H K t|.
Proof. by rewrite -translated_apex cardJg. Qed.

Definition translated_iso := raw_onto_iso (raw_equal_rank_image translated_arrow translated_rank).

Lemma translated_iso_first :
    Category.compose (iso_hom translated_iso)
      (orbit_class (inclusion_left F H K t)) =
    orbit_class (inclusion_left F H K (h*t*k)).
Proof.
change (orbit_compose (orbit_class translated_arrow)
  (orbit_class (inclusion_left F H K t)) = orbit_class (inclusion_left F H K (h*t*k))).
rewrite orbit_compose_class; apply/eqP; rewrite eq_sym; apply/eqP.
apply/orbit_class_eq; apply/exists_inP; exists h=> //.
apply/forall_inP=> x hx; apply/eqP.
change (DPFusion.compose (val translated_arrow) (val (inclusion_left F H K t)) x = (val (inclusion_left F H K (h*t*k)) x)^h).
rewrite DPFusion.compose_in // /translated_arrow /inclusion_left /=.
rewrite conjugation_in // inclusion_in ?(map_into (val translated_arrow) hx) //.
by rewrite inclusion_in.
by rewrite -translated_apex mem_conjg conjgK.
Qed.

Lemma translated_iso_second :
    Category.compose (iso_hom translated_iso)
      (orbit_class (inclusion_right F H K t)) =
    orbit_class (inclusion_right F H K (h*t*k)).
Proof.
change (orbit_compose (orbit_class translated_arrow)
  (orbit_class (inclusion_right F H K t)) = orbit_class (inclusion_right F H K (h*t*k))).
rewrite orbit_compose_class; apply/orbit_class_eq; apply/exists_inP; exists k=> //.
apply/forall_inP=> x hx; apply/eqP.
change (val (inclusion_right F H K (h*t*k)) x = (DPFusion.compose (val translated_arrow) (val (inclusion_right F H K t)) x)^k).
rewrite DPFusion.compose_in // /translated_arrow /inclusion_right /=.
rewrite !conjugation_in //.
- by rewrite !conjgM.
- by rewrite -translated_apex mem_conjg conjgK.
Qed.
End Geometry.

Section Coefficients.
Variable S : finGroupType.
Variable F : system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Variables H K : {group S}.

Definition inclusion_summand (t : S) (x : pair_value M H) :=
  pair_push M (orbit_class (inclusion_right F H K t))
    (pair_pull M (orbit_class (inclusion_left F H K t)) x).

Lemma translated_summand h t k : h \in H -> k \in K ->
    forall x, inclusion_summand (h*t*k) x = inclusion_summand t x.
Proof.
move=> hH kK x.
apply: (@pair_span_iso_invariance R (orbit_category F) M _ _ H K
  (translated_iso F t hH kK) _ _ _ _
  (translated_iso_first F t hH kK) (translated_iso_second F t hH kK) x).
Qed.

Lemma same_double_coset_summand s t :
    double_coset H K s = double_coset H K t ->
    forall x, inclusion_summand s x = inclusion_summand t x.
Proof.
move=> he x.
have hm : s \in double_coset H K t.
  by rewrite -he; exact: trace_double_coset_contains_representative.
have /double_cosetP[h [k [hH [kK ->]]]] := hm.
exact: translated_summand.
Qed.
End Coefficients.
End DPMackeyRepresentatives.

Print Assumptions DPMackeyRepresentatives.same_double_coset_summand.






