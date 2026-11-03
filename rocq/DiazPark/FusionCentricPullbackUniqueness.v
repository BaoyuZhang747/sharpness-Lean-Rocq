From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import FusionMaps FusionSystems FusionOrbit FusionMackeyShape
  FusionCentricPullbackGeometry.
Import DPFusion DPFusionOrbit DPFusionMackey DPFusionCentricPullbackGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricPullbackUniqueness.
Section Uniqueness.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q T X : {group S}.
Variables (f : DPFusionSystem.arrow F P T) (g : DPFusionSystem.arrow F Q T).
Variables t u : S.
Variables (h : DPFusionSystem.arrow F X (raw_apex f g t))
  (k : DPFusionSystem.arrow F X (raw_apex f g u)).
Hypothesis he : orbit_compose (orbit_class h) (orbit_class (raw_left f g t)) =
  orbit_compose (orbit_class k) (orbit_class (raw_left f g u)).
Hypothesis ke : orbit_compose (orbit_class h) (orbit_class (raw_right f g t)) =
  orbit_compose (orbit_class k) (orbit_class (raw_right f g u)).

Lemma raw_left_conjugator : exists a : S, a \in image (val f) /\
    {in X, forall x, (val k) x = (val h) x ^ a}.
Proof.
move: he; rewrite !orbit_compose_class=> /orbit_class_eq/exists_inP[a Pa /forall_inP ha].
exists ((val f) a); split; first exact: image_mem Pa.
move=> x Xx.
have hh := congr1 (map_fun (val f)) (eqP (ha x Xx)).
change ((val f) (DPFusion.compose (val k) (val (raw_left f g u)) x) =
  (val f) ((DPFusion.compose (val h) (val (raw_left f g t)) x)^a)) in hh.
rewrite (@compose_in S X (raw_apex f g u) P (val k) (val (raw_left f g u)) x Xx)
  (@compose_in S X (raw_apex f g t) P (val h) (val (raw_left f g t)) x Xx) in hh.
have ht := map_into (val h) Xx.
have hu := map_into (val k) Xx.
have hj := morphJ (map_morphism (val f)) (map_into (val (raw_left f g t)) ht) Pa.
rewrite !map_morphismE in hj.
rewrite hj
  !raw_left_triangle // in hh.
Qed.

Lemma raw_right_conjugator : exists b : S, b \in image (val g) /\
    {in X, forall x, (val k) x ^ u = ((val h) x ^ t) ^ b}.
Proof.
move: ke; rewrite !orbit_compose_class=> /orbit_class_eq/exists_inP[b Qb /forall_inP hb].
exists ((val g) b); split; first exact: image_mem Qb.
move=> x Xx.
have hh := congr1 (map_fun (val g)) (eqP (hb x Xx)).
change ((val g) (DPFusion.compose (val k) (val (raw_right f g u)) x) =
  (val g) ((DPFusion.compose (val h) (val (raw_right f g t)) x)^b)) in hh.
rewrite (@compose_in S X (raw_apex f g u) Q (val k) (val (raw_right f g u)) x Xx)
  (@compose_in S X (raw_apex f g t) Q (val h) (val (raw_right f g t)) x Xx) in hh.
have ht := map_into (val h) Xx.
have hu := map_into (val k) Xx.
have hj := morphJ (map_morphism (val g)) (map_into (val (raw_right f g t)) ht) Qb.
rewrite !map_morphismE in hj.
rewrite hj
  !raw_right_triangle // in hh.
Qed.

Theorem raw_factor_double_coset (cX : DPFusionSystem.centric F X) :
    double_coset (image (val f)) (image (val g)) u =
    double_coset (image (val f)) (image (val g)) t.
Proof.
have [a [Ha ha]] := raw_left_conjugator.
have [b [Kb hb]] := raw_right_conjugator.
exact (@conjugator_double_coset S F (image (val f)) (image (val g)) X t u h k cX a b Ha Kb ha hb).
Qed.

End Uniqueness.

Section EqualIndex.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variables P Q T X : {group S}.
Variables (f : DPFusionSystem.arrow F P T) (g : DPFusionSystem.arrow F Q T).
Variable t : S.
Variables (h k : DPFusionSystem.arrow F X (raw_apex f g t)).
Hypothesis cX : DPFusionSystem.centric F X.
Hypothesis he : orbit_compose (orbit_class h) (orbit_class (raw_left f g t)) =
  orbit_compose (orbit_class k) (orbit_class (raw_left f g t)).
Hypothesis ke : orbit_compose (orbit_class h) (orbit_class (raw_right f g t)) =
  orbit_compose (orbit_class k) (orbit_class (raw_right f g t)).

Theorem raw_same_representative_unique : orbit_class h = orbit_class k.
Proof.
have [a [Ha ha]] := raw_left_conjugator he.
have [b [Kb hb]] := raw_right_conjugator ke.
have Aa := @same_representative_conjugator S F (image (val f)) (image (val g))
  X t t h k cX a b Ha Kb ha hb erefl.
apply/orbit_class_eq; apply/exists_inP; exists a=> //.
apply/forall_inP=> x Xx; apply/eqP; exact: ha x Xx.
Qed.
End EqualIndex.
End DPFusionCentricPullbackUniqueness.
