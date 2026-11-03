From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOrbitRanks
  FusionMackeyShape FusionMackeyRepresentatives FusionMackeyDoubleCosetTransport
  MackeyPair MackeyPairSpanIso.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionRanks DPFusionMackey
  DPMackeyRepresentatives DPMackeyDoubleCosetTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionMackeyFullGeometry.
Section Geometry.
Variable S : finGroupType.
Variable F : system S.

Lemma conjugation_image (P T : {group S}) (f : arrow F P T) a
    (hf : {in P, val f =1 (fun x => x ^ a)}) :
  DPFusion.image (val f) = (P :^ a)%G.
Proof.
apply: val_inj; apply/setP=> y; apply/morphimP/imsetP.
- move=> [x Px _ ->]; exists x=> //; exact: hf.
- move=> [x Px ->]; exists x=> //; symmetry; exact: hf.
Qed.

Lemma conjugation_inverse (P T : {group S}) (f : arrow F P T) a
    (hf : {in P, val f =1 (fun x => x ^ a)}) y :
  y \in DPFusion.image (val f) -> DPFusion.inverse (val f) y = y ^ a^-1.
Proof.
move=> /morphimP[x Px _ ->]; rewrite inverse_cancel //.
change (x = (val f x) ^ a^-1).
by rewrite hf // conjgK.
Qed.

Variables P Q T : {group S}.
Variables (f : arrow F P T) (g : arrow F Q T).
Variables a b : S.
Hypotheses (hf : {in P, val f =1 (fun x => x ^ a)})
  (hg : {in Q, val g =1 (fun x => x ^ b)}).

Lemma raw_apex_conjugation t :
  raw_apex f g t :^ a^-1 = inclusion_apex P Q (untranslate a b t).
Proof.
exact: (translated_apex (conjugation_image hf) (conjugation_image hg)).
Qed.
Lemma raw_apex_conjugation_sub t :
  raw_apex f g t :^ a^-1 \subset inclusion_apex P Q (untranslate a b t).
Proof. by rewrite raw_apex_conjugation. Qed.

Definition raw_apex_arrow t : arrow F (raw_apex f g t)
    (inclusion_apex P Q (untranslate a b t)) :=
  Sub (conjugation (raw_apex_conjugation_sub t))
    (conjugation_closed F (raw_apex_conjugation_sub t)).

Lemma raw_apex_rank t :
  #|raw_apex f g t| = #|inclusion_apex P Q (untranslate a b t)|.
Proof. by rewrite -raw_apex_conjugation cardJg. Qed.

Definition raw_apex_iso t :=
  raw_onto_iso (raw_equal_rank_image (raw_apex_arrow t) (raw_apex_rank t)).

Lemma raw_apex_first t :
  Category.compose (iso_hom (raw_apex_iso t))
    (orbit_class (inclusion_left F P Q (untranslate a b t))) = orbit_class (raw_left f g t).
Proof.
change (orbit_compose (orbit_class (raw_apex_arrow t))
  (orbit_class (inclusion_left F P Q (untranslate a b t))) = orbit_class (raw_left f g t)).
rewrite orbit_compose_class; apply: congr1; apply: arrow_ext=> x Ax.
change (DPFusion.compose (val (raw_apex_arrow t))
  (val (inclusion_left F P Q (untranslate a b t))) x = val (raw_left f g t) x).
rewrite compose_in // raw_left_value //.
rewrite /raw_apex_arrow /inclusion_left /= conjugation_in // inclusion_in.
- symmetry; exact: (@conjugation_inverse P T f a hf x (subsetP (raw_apex_left f g t) x Ax)).
- by rewrite -raw_apex_conjugation mem_conjg conjgK.
Qed.

Lemma raw_apex_second t :
  Category.compose (iso_hom (raw_apex_iso t))
    (orbit_class (inclusion_right F P Q (untranslate a b t))) = orbit_class (raw_right f g t).
Proof.
change (orbit_compose (orbit_class (raw_apex_arrow t))
  (orbit_class (inclusion_right F P Q (untranslate a b t))) = orbit_class (raw_right f g t)).
rewrite orbit_compose_class; apply: congr1; apply: arrow_ext=> x Ax.
change (DPFusion.compose (val (raw_apex_arrow t))
  (val (inclusion_right F P Q (untranslate a b t))) x = val (raw_right f g t) x).
rewrite compose_in // raw_right_value //.
rewrite /raw_apex_arrow /inclusion_right /= !conjugation_in.
- have hx : x ^ t \in DPFusion.image (val g).
    move: Ax; by rewrite /raw_apex inE mem_conjgV => /andP[_].
  rewrite (conjugation_inverse hg hx) /untranslate -!conjgM -!mulgA mulKg.
  reflexivity.
- exact Ax.
- by rewrite -raw_apex_conjugation mem_conjg conjgK.
all: try exact Ax.
Qed.

Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Lemma conjugated_raw_summand t x :
  pair_push M (orbit_class (raw_right f g t))
    (pair_pull M (orbit_class (raw_left f g t)) x) =
  @inclusion_summand S F R M P Q (untranslate a b t) x.
Proof.
exact: (@pair_span_iso_invariance R (orbit_category F) M _ _ P Q
  (raw_apex_iso t) _ _ _ _ (raw_apex_first t) (raw_apex_second t) x).
Qed.
End Geometry.
End DPFusionMackeyFullGeometry.
