From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionMackeyShape
  TraceNormalizerCosets FusionCentricPullbackExistence FusionCentricBasics.
Import DPFusion DPFusionOrbit DPFusionMackey DPFusionCentricPullbackExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricPullbackFactors.
Section Factors.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q T X : {group S}.
Variables (f : DPFusionSystem.arrow F P T) (g : DPFusionSystem.arrow F Q T).

Lemma translate_factor_eq t u a b (Ha : a \in image (val f)) (Kb : b \in image (val g))
    (et : t = a*u*b) (h : DPFusionSystem.arrow F X (raw_apex f g t)) :
    exists h0 : DPFusionSystem.arrow F X (raw_apex f g u),
      orbit_compose (orbit_class h0) (orbit_class (raw_left f g u)) =
        orbit_compose (orbit_class h) (orbit_class (raw_left f g t)) /\
      orbit_compose (orbit_class h0) (orbit_class (raw_right f g u)) =
        orbit_compose (orbit_class h) (orbit_class (raw_right f g t)).
Proof. subst t; exact: raw_translate_factor Ha Kb h. Qed.

Theorem canonical_factor_exists (a : DPFusionSystem.arrow F X P)
    (b : DPFusionSystem.arrow F X Q)
    (he : orbit_compose (orbit_class a) (orbit_class f) =
      orbit_compose (orbit_class b) (orbit_class g)) :
    exists i : raw_index f g,
    exists h : DPFusionSystem.arrow F X (raw_apex f g (double_coset_representative i)),
      orbit_compose (orbit_class h) (orbit_class (raw_left f g (double_coset_representative i))) = orbit_class a /\
      orbit_compose (orbit_class h) (orbit_class (raw_right f g (double_coset_representative i))) = orbit_class b.
Proof.
move: he; rewrite !orbit_compose_class=> /orbit_class_eq/exists_inP[t Tt /forall_inP ht].
have same : {in X, forall x,
  DPFusion.compose (val b) (val g) x = (DPFusion.compose (val a) (val f) x)^t}.
  move=> x Xx; exact (eqP (ht x Xx)).
pose h := @raw_pointwise_factor S F P Q T X f g a b t same.
have hl : orbit_compose (orbit_class h) (orbit_class (raw_left f g t)) = orbit_class a.
  by rewrite orbit_compose_class (@raw_pointwise_left S F P Q T X f g a b t same).
have hr : orbit_compose (orbit_class h) (orbit_class (raw_right f g t)) = orbit_class b.
  by rewrite orbit_compose_class (@raw_pointwise_right S F P Q T X f g a b t same).
have mi : double_coset (image (val f)) (image (val g)) t \in
    (double_coset (image (val f)) (image (val g))) @: T.
  apply/imsetP; by exists t.
pose i : raw_index f g := Sub (double_coset (image (val f)) (image (val g)) t) mi.
have ti : t \in double_coset (image (val f)) (image (val g)) (double_coset_representative i).
  rewrite double_coset_representative_set /i /=.
  exact: trace_double_coset_contains_representative.
have /double_cosetP[c [d [Hc [Kd et]]]] := ti.
have [h0 [h0l h0r]] := translate_factor_eq Hc Kd et h.
exists i,h0; split; [by rewrite h0l hl | by rewrite h0r hr].
Qed.

Lemma factor_apex_centric t (h : DPFusionSystem.arrow F X (raw_apex f g t)) :
    DPFusionSystem.centric F X -> DPFusionSystem.centric F (raw_apex f g t).
Proof.
move=> cX; exact (DPFusionCentricBasics.centric_overgroup (image_sub (val h))
  (DPFusionCentricBasics.centric_image (valP h) cX)).
Qed.
End Factors.
End DPFusionCentricPullbackFactors.
