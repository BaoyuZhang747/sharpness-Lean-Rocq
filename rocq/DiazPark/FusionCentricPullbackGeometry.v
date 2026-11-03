From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionMackeyShape
  FusionCentricBasics FusionCentricCriterion.
Import DPFusion DPFusionOrbit DPFusionMackey.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricPullbackGeometry.
Section DoubleCosets.
Variable S : finGroupType.
Variables H K : {group S}.
Lemma double_coset_translate h t k : h \in H -> k \in K ->
    double_coset H K (h*t*k) = double_coset H K t.
Proof.
move=> Hh Kk; apply/setP=> x; apply/double_cosetP/double_cosetP.
- move=> [a [b [Ha [Kb ->]]]].
  exists (a*h), (k*b); split; first exact: groupM Ha Hh.
  split; first exact: groupM Kk Kb. by rewrite !mulgA.
- move=> [a [b [Ha [Kb ->]]]].
  exists (a*h^-1), (k^-1*b); split; first by rewrite groupM // groupV.
  split; first by rewrite groupM ?groupV.
  by rewrite !mulgA mulgVK mulgK.
Qed.
End DoubleCosets.

Section Rigidity.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables H K X : {group S}.
Variable t u : S.
Variable h : DPFusionSystem.arrow F X (inclusion_apex H K t).
Variable k : DPFusionSystem.arrow F X (inclusion_apex H K u).
Hypothesis cX : DPFusionSystem.centric F X.
Variables a b : S.
Hypotheses (Ha : a \in H) (Kb : b \in K).
Hypothesis left_eq : {in X, forall x, (val k) x = (val h) x ^ a}.
Hypothesis right_eq : {in X, forall x, (val k) x ^ u = ((val h) x ^ t) ^ b}.
Definition conjugation_ratio := a*u*(t*b)^-1.

Lemma ratio_centralizes : conjugation_ratio \in 'C(image (val h)).
Proof.
apply/centP=> z /morphimP[x Xx _ hz]; apply/commgP; rewrite commg1_sym; apply/conjg_fixP.
change (z = (val h) x) in hz; rewrite hz /conjugation_ratio !conjgM.
by rewrite -(@left_eq x Xx) (@right_eq x Xx) -(conjgM ((val h) x) t b) conjgK.
Qed.

Lemma ratio_in_apex : conjugation_ratio \in inclusion_apex H K t.
Proof.
have cI := DPFusionCentricBasics.centric_image (valP h) cX.
exact (subsetP (image_sub (val h)) _
  (subsetP (DPFusionCentricCriterion.centric_self_centralizing cI) _ ratio_centralizes)).
Qed.

Lemma conjugator_double_coset : double_coset H K u = double_coset H K t.
Proof.
have Hc : conjugation_ratio \in H := subsetP (inclusion_apex_left H K t) _ ratio_in_apex.
have e : u = (a^-1*conjugation_ratio)*t*b.
  by rewrite /conjugation_ratio !mulgA mulVg mul1g -!mulgA mulVg mulg1.
rewrite e; apply: double_coset_translate=> //.
by rewrite groupM ?groupV.
Qed.

Lemma same_representative_conjugator : u = t -> a \in inclusion_apex H K t.
Proof.
move=> ut.
have hc : conjugation_ratio * (t*b) = a*t by rewrite /conjugation_ratio mulgKV ut.
have he : a^t = conjugation_ratio^t*b.
  by rewrite !conjgE -mulgA -hc !mulgA.
have Kc : conjugation_ratio^t \in K.
  apply: (subsetP (inclusion_apex_right H K t)); by rewrite memJ_conjg ratio_in_apex.
rewrite /inclusion_apex inE Ha mem_conjgV he.
exact: groupM Kc Kb.
Qed.
End Rigidity.
End DPFusionCentricPullbackGeometry.
