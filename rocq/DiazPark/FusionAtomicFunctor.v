From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow generic_quotient.
From DiazPark Require Import Category GroupOrbitCategory GroupOrbitCollections GroupOrbitPReflection
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionAtomicFunctorPreimages FusionAtomicFunctorFixed.
Import DPFusion DPFusionOrbit DPFusionAtomicPreimages DPFusionAtomicFixed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionAtomicFunctor.
Section Functor.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable Q : {group S}.
Hypothesis centricQ : DPFusionSystem.centric F Q.
Local Notation G := (outer_type F Q).
Local Notation T := (ambient_outer F Q).
Definition domain := DPGroupOrbitP.bounded_orbit_category p T.
Local Notation CC := (centric_orbit_category F).
Local Notation OC := (DPFusionOrbit.orbit_category F).
Local Notation QH H := (@preimage S F Q H).
Local Notation iH H := (inclusion_orbit centricQ H).
Local Notation orb g := (@outer_orbit S F Q g).

Lemma orbit_assoc (A B C D : {group S}) (f : orbit_hom F A B)
    (g : orbit_hom F B C) (h : orbit_hom F C D) :
  orbit_compose (orbit_compose f g) h = orbit_compose f (orbit_compose g h).
Proof. exact: (@Category.compose_assoc OC A B C D f g h). Qed.
Lemma orbit_id_left (A B : {group S}) (f : orbit_hom F A B) :
  orbit_compose (orbit_identity F A) f = f.
Proof. exact: (@Category.compose_id_left OC A B f). Qed.
Lemma orbit_id_right (A B : {group S}) (f : orbit_hom F A B) :
  orbit_compose f (orbit_identity F B) = f.
Proof. exact: (@Category.compose_id_right OC A B f). Qed.

Definition object (H : domain) : centric_object F :=
  Sub (QH (val H)) (preimage_centric centricQ (val H)).
Lemma object_bound (H : domain) : val H \subset T.
Proof. exact: (andP (valP H)).2. Qed.

Lemma lift_exists (H : {group G}) (P : {group S}) (f : orbit_hom F Q P)
    (hf : fixed H f) : exists b : orbit_hom F (QH H) P, restriction centricQ b == f.
Proof.
have [b eb] := fixed_extension sat centricQ hf; exists b; exact/eqP.
Qed.

Definition lift (H : {group G}) (P : {group S}) (f : orbit_hom F Q P)
    (hf : fixed H f) : orbit_hom F (QH H) P :=
  xchoose (lift_exists hf).
Lemma lift_spec (H : {group G}) (P : {group S}) (f : orbit_hom F Q P) (hf : fixed H f) :
  restriction centricQ (lift hf) = f.
Proof. exact: eqP (xchooseP (lift_exists hf)). Qed.

Definition transported (H K : domain) (g : DPGroupOrbit.transporter (val H) (val K)) :=
  orbit_compose (orb (val g)) (iH (val K)).
Lemma transported_fixed (H K : domain) (g : DPGroupOrbit.transporter (val H) (val K)) :
  fixed (val H) (transported g).
Proof.
move=> h Hh.
have hH : h ^ (val g) \in (val H) :^ (val g) by rewrite memJ_conjg.
 have Khg : h ^ (val g) \in val K := subsetP (valP g) _ hH.
have fixK := inclusion_fixed centricQ (object_bound K) Khg.
change (orbit_compose (orb h) (orbit_compose (orb (val g)) (iH (val K))) = transported g).
rewrite -orbit_assoc -outer_orbit_mul.
have ehg : h * val g = val g * (h ^ val g) by rewrite conjgE !mulgA mulgV mul1g.
rewrite ehg outer_orbit_mul orbit_assoc fixK.
by [].
Qed.

Definition raw_map (H K : domain) (g : DPGroupOrbit.transporter (val H) (val K)) :
  hom CC (object H) (object K) := lift (transported_fixed g).
Lemma raw_map_spec (H K : domain) (g : DPGroupOrbit.transporter (val H) (val K)) :
  restriction centricQ (raw_map g) = transported g.
Proof. exact: lift_spec. Qed.

Lemma transported_related (H K : domain) (g g' : DPGroupOrbit.transporter (val H) (val K)) :
  DPGroupOrbit.related g g' -> transported g = transported g'.
Proof.
move=> /eqP he.
have hh : val g' \in val g *: val K by rewrite he; exact: lcoset_refl.
have /lcosetP[k Kk eg] := hh.
rewrite /transported eg outer_orbit_mul.
change (orbit_compose (orb (val g)) (iH (val K)) =
  orbit_compose (orbit_compose (orb (val g)) (orb k)) (iH (val K))).
by rewrite orbit_assoc (inclusion_fixed centricQ (object_bound K) Kk).
Qed.

Lemma raw_map_related (H K : domain) (g g' : DPGroupOrbit.transporter (val H) (val K)) :
  DPGroupOrbit.related g g' -> raw_map g = raw_map g'.
Proof.
move=> he; apply: (@restriction_injective S F p pS sat Q centricQ (val H) (QH (val K))).
exact: eq_trans (raw_map_spec g) (eq_trans (transported_related he) (esym (raw_map_spec g'))).
Qed.

Definition arrow (H K : domain) (f : hom domain H K) : hom CC (object H) (object K) :=
  raw_map (repr f).
Lemma arrow_class (H K : domain) (g : DPGroupOrbit.transporter (val H) (val K)) :
  arrow (DPGroupOrbit.orbit_class g) = raw_map g.
Proof. exact: raw_map_related (DPGroupOrbit.representative_related g). Qed.

Lemma arrow_identity (H : domain) : arrow (@Category.identity domain H) = @Category.identity CC (object H).
Proof.
change (arrow (DPGroupOrbit.orbit_class (DPGroupOrbit.transporter_identity (val H))) = orbit_identity F (QH (val H))).
rewrite arrow_class; apply: (@restriction_injective S F p pS sat Q centricQ (val H) (QH (val H))).
rewrite raw_map_spec /transported /= outer_orbit_one.
change (orbit_compose (DPFusionOrbit.orbit_identity F Q) (iH (val H)) =
  orbit_compose (iH (val H)) (DPFusionOrbit.orbit_identity F (QH (val H)))).
by rewrite orbit_id_left orbit_id_right.
Qed.

Lemma arrow_compose (H K L : domain) (f : hom domain H K) (g : hom domain K L) :
  arrow (@Category.compose domain H K L f g) = @Category.compose CC (object H) (object K) (object L) (arrow f) (arrow g).
Proof.
move: f; apply: quotW=> f; move: g; apply: quotW=> g.
change (arrow (DPGroupOrbit.orbit_compose (DPGroupOrbit.orbit_class f) (DPGroupOrbit.orbit_class g)) = orbit_compose (arrow (DPGroupOrbit.orbit_class f)) (arrow (DPGroupOrbit.orbit_class g))).
rewrite DPGroupOrbit.orbit_compose_class (arrow_class (DPGroupOrbit.transporter_compose f g)) (arrow_class f) (arrow_class g).
apply: (@restriction_injective S F p pS sat Q centricQ (val H) (QH (val L))).
rewrite raw_map_spec restriction_postcompose raw_map_spec /transported /=.
rewrite outer_orbit_mul.
change (orbit_compose (orbit_compose (orb (val f)) (orb (val g))) (iH (val L)) =
  orbit_compose (orbit_compose (orb (val f)) (iH (val K))) (raw_map g)).
rewrite !orbit_assoc.
congr (orbit_compose _ _).
exact: esym (raw_map_spec g).
Qed.

Definition comparison_functor : functor domain CC :=
  @Build_functor domain CC object (fun H K f => arrow f) arrow_identity arrow_compose.

Lemma comparison_restriction (H K : domain) (g : DPGroupOrbit.transporter (val H) (val K)) :
  restriction centricQ (fmap comparison_functor (DPGroupOrbit.orbit_class g)) =
    orbit_compose (orb (val g)) (iH (val K)).
Proof. change (restriction centricQ (arrow (DPGroupOrbit.orbit_class g)) = orbit_compose (orb (val g)) (iH (val K))).
by rewrite arrow_class raw_map_spec.
Qed.

End Functor.
End DPFusionAtomicFunctor.










