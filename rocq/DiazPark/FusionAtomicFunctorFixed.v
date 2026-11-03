From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionSaturation
  FusionOuterOrbit FusionOuterAction FusionAtomicFunctorPreimages
  FusionCentricHomAction FusionCentricHomRestriction FusionCentricNormalizerExtension.
Import DPFusion DPFusionOrbit DPFusionAtomicPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionAtomicFixed.
Section Fixed.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable Q : {group S}.
Hypothesis centricQ : DPFusionSystem.centric F Q.
Local Notation G := (outer_type F Q).
Local Notation T := (ambient_outer F Q).
Local Notation QH H := (@preimage S F Q H).

Definition outer_orbit (g : G) : orbit_hom F Q Q :=
  DPFusionOuterAction.outer_orbit F (val g).
Lemma outer_orbit_one : outer_orbit 1 = orbit_identity F Q.
Proof. exact: DPFusionOuterAction.outer_orbit_one. Qed.
Lemma outer_orbit_mul (g h : G) :
  outer_orbit (g*h) = orbit_compose (outer_orbit g) (outer_orbit h).
Proof. exact: DPFusionOuterAction.outer_orbit_mul (valP g) (valP h). Qed.
Lemma outer_orbit_theta n : n \in 'N(Q) ->
  outer_orbit (theta F Q n) = DPFusionOuterOrbit.aut_orbit F Q (conj_aut Q n).
Proof.
move=> Nn; rewrite /outer_orbit theta_value //.
exact: DPFusionOuterAction.outer_orbit_coset (conjugation_allowed F Nn).
Qed.

Definition inclusion_orbit (H : {group G}) : orbit_hom F Q (QH H) :=
  orbit_class (Sub (DPFusion.inclusion (source_sub_preimage centricQ H))
    (DPFusionSystem.inclusion_allowed F (source_sub_preimage centricQ H))).
Definition restriction (H : {group G}) (P : {group S}) (f : orbit_hom F (QH H) P) :=
  orbit_compose (inclusion_orbit H) f.
Definition fixed (H : {group G}) (P : {group S}) (f : orbit_hom F Q P) :=
  forall h, h \in H -> orbit_compose (outer_orbit h) f = f.

Lemma restriction_injective (H : {group G}) (P : {group S}) :
  injective (@restriction H P).
Proof.
exact: (@DPFusionCentricHomRestriction.restriction_injective S F p pS sat Q (QH H) P
  (source_sub_preimage centricQ H) (@preimage_sub_normalizer S F Q H) centricQ).
Qed.

Lemma restriction_fixed (H : {group G}) (sHT : H \subset T)
    (P : {group S}) (f : orbit_hom F (QH H) P) : fixed H (restriction f).
Proof.
have hi := @DPFusionCentricHomRestriction.restriction_fixed S F Q (QH H) P
  (source_sub_preimage centricQ H) (@preimage_sub_normalizer S F Q H) f.
have hf := (afixP hi).
move=> h Hh.
have hI : h \in theta F Q @* QH H by rewrite preimage_image.
have /morphimP[n Nn hn en] := hI.
have nQH : n \in QH H := hn.
pose nn : [subg QH H] := Sub n nQH.
have hnall : nn^-1 \in [set: [subg QH H]] by rewrite inE.
have he := hf nn^-1 hnall.
change (@DPFusionCentricHomAction.hom_action S F Q P (QH H) (restriction f) nn^-1 = restriction f) in he.
rewrite /DPFusionCentricHomAction.hom_action invgK /DPFusionCentricHomAction.conjugation_orbit /= in he.
by rewrite en outer_orbit_theta.
Qed.

Lemma fixed_extension (H : {group G}) (P : {group S}) (f : orbit_hom F Q P) :
  fixed H f -> exists b : orbit_hom F (QH H) P, restriction b = f.
Proof.
move: f; apply: quotW=> f hf.
have compat : forall n, n \in QH H -> exists t, t \in P /\
    {in Q, forall x, (val f) (x ^ n) = ((val f) x) ^ t}.
  move=> n hn.
  have Nn := subsetP (@preimage_sub_normalizer S F Q H) n hn.
  have thH : theta F Q n \in H := (morphpreP hn).2.
  have e := hf _ thH; rewrite outer_orbit_theta // /DPFusionOuterOrbit.aut_orbit orbit_compose_class in e.
  have [t [Pt ht]] := proj1 (orbit_class_eq_iff _ _) (esym e).
  exists t; split=> // x Qx.
  have h := ht x Qx.
  change (DPFusion.compose (DPFusionOuterOrbit.aut_map F Q (conj_aut Q n)) (val f) x = ((val f) x)^t) in h.
  by rewrite DPFusion.compose_in // DPFusionOuterOrbit.aut_mapE ?conjugation_allowed //
    norm_conj_autE // in h.
have [b [hb he]] := @DPFusionCentricNormalizerExtension.centric_normalizer_extension
  S F p sat Q (QH H) P (val f) (valP f) centricQ
  (source_sub_preimage centricQ H) (@preimage_sub_normalizer S F Q H) compat.
pose bb : DPFusionSystem.arrow F (QH H) P := Sub b hb.
exists (orbit_class bb); rewrite /restriction /inclusion_orbit orbit_compose_class.
apply: congr1; apply: val_inj; apply: DPFusion.map_ext=> x Qx.
change (DPFusion.compose (DPFusion.inclusion (source_sub_preimage centricQ H)) b x = (val f) x).
by rewrite DPFusion.compose_in // DPFusion.inclusion_in // he.
Qed.

Lemma inclusion_fixed (H : {group G}) (sHT : H \subset T) : fixed H (inclusion_orbit H).
Proof.
have h := restriction_fixed sHT (orbit_identity F (QH H)).
have e : restriction (orbit_identity F (QH H)) = inclusion_orbit H :=
  @Category.compose_id_right (orbit_category F) Q (QH H) (inclusion_orbit H).
by rewrite e in h.
Qed.

Lemma restriction_postcompose (H : {group G}) (P R : {group S})
    (f : orbit_hom F (QH H) P) (g : orbit_hom F P R) :
  restriction (orbit_compose f g) = orbit_compose (restriction f) g.
Proof. exact: esym (@Category.compose_assoc (orbit_category F) _ _ _ _ _ _ _). Qed.

End Fixed.
End DPFusionAtomicFixed.



