(** Stability under every fusion isomorphism follows from invariance under
    centric automorphisms, using the actual finite Alperin word theorem. *)

From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionConjugacy FusionSaturation FusionSaturationImage FusionAlperinWords FusionAlperinTheorem
  MackeyPair FusionMackeyShape.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionAlperinWords.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionStable.
Section Stable.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).

Definition raw_pull (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :=
  pair_pull M (DPFusionOrbit.orbit_class f).

Definition inclusion (P Q : {group S}) (h : P \subset Q) :=
  DPFusionMackey.inclusion_arrow F h.

Definition restrict_top (P : {group S}) := raw_pull (inclusion (subsetT P)).

Lemma raw_pull_composition (P Q T : {group S})
    (f : DPFusionSystem.arrow F P Q) (g : DPFusionSystem.arrow F Q T) x :
    raw_pull (DPFusionSystem.arrow_compose f g) x = raw_pull f (raw_pull g x).
Proof.
  rewrite /raw_pull -DPFusionOrbit.orbit_compose_class.
  exact (@pair_pull_comp R (DPFusionOrbit.orbit_category F) M P Q T
    (DPFusionOrbit.orbit_class f) (DPFusionOrbit.orbit_class g) x).
Qed.

Lemma inclusion_composition (P Q T : {group S})
    (hPQ : P \subset Q) (hQT : Q \subset T) :
    DPFusionSystem.arrow_compose (inclusion hPQ) (inclusion hQT) =
      inclusion (subset_trans hPQ hQT).
Proof.
  apply DPFusionSystem.arrow_ext. intros x hx.
  rewrite /DPFusionSystem.arrow_compose /inclusion /DPFusionMackey.inclusion_arrow /=.
  by rewrite DPFusion.compose_in // !DPFusion.inclusion_in // (subsetP hPQ).
Qed.

Lemma restriction_top_factor (P Q : {group S}) (h : P \subset Q) x :
    restrict_top P x = raw_pull (inclusion h) (restrict_top Q x).
Proof.
  rewrite /restrict_top -raw_pull_composition inclusion_composition.
  congr (raw_pull _ x). apply val_inj. apply DPFusion.map_ext.
  intros a ha. by rewrite !DPFusion.inclusion_in.
Qed.

Definition centric_invariant (x : pair_value M [set: S]%G) : Prop :=
  forall (P : {group S}) (a : DPFusionSystem.arrow F P P),
    DPFusionSystem.centric F P -> raw_pull a (restrict_top P x) = restrict_top P x.

Definition stable_element (x : pair_value M [set: S]%G) : Prop :=
  forall (P Q : {group S}) (f : DPFusionSystem.arrow F P Q),
    DPFusion.image (val f) = Q ->
    raw_pull f (restrict_top Q x) = restrict_top P x.

Lemma stable_all_arrows (x : pair_value M [set: S]%G) (hx : stable_element x)
    (P Q : {group S}) (f : DPFusionSystem.arrow F P Q) :
    raw_pull f (restrict_top Q x) = restrict_top P x.
Proof.
  pose fi := (Sub (DPFusion.to_image (val f)) (DPFusionSystem.image_closed (valP f)) :
    DPFusionSystem.arrow F P (DPFusion.image (val f))).
  have he : DPFusionSystem.arrow_compose fi
      (inclusion (DPFusion.image_sub (val f))) = f.
  { apply val_inj. exact (DPFusion.image_factorization (val f)). }
  rewrite -he raw_pull_composition -(restriction_top_factor (DPFusion.image_sub (val f))).
  apply hx. exact (DPFusionSaturationImage.image_to_image (val f)).
Qed.

Lemma step_square (a : generator F) (P Q : {group S}) (r : restriction a P Q) :
    DPFusionSystem.arrow_compose (Sub (step_map r) (step_allowed r))
      (inclusion (step_target r)) =
    DPFusionSystem.arrow_compose (inclusion (step_source r))
      (Sub (generator_map a) (generator_allowed a)).
Proof.
  apply DPFusionSystem.arrow_ext. intros x hx.
  rewrite /DPFusionSystem.arrow_compose /inclusion /DPFusionMackey.inclusion_arrow /=.
  rewrite !DPFusion.compose_in // !DPFusion.inclusion_in ?DPFusion.map_into //.
  exact (step_agrees r hx).
Qed.

Lemma centric_invariant_step (x : pair_value M [set: S]%G)
    (hx : centric_invariant x) (a : generator F) (P Q : {group S})
    (r : restriction a P Q) :
    raw_pull (Sub (step_map r) (step_allowed r)) (restrict_top Q x) = restrict_top P x.
Proof.
  rewrite (restriction_top_factor (step_target r)) -raw_pull_composition step_square
    raw_pull_composition (hx _ _ (generator_centric a)).
  exact (esym (restriction_top_factor (step_source r) x)).
Qed.

Lemma centric_invariant_word (x : pair_value M [set: S]%G)
    (hx : centric_invariant x) P Q l (w : @word S F P Q l) :
    raw_pull (Sub (evaluation w) (evaluation_allowed w)) (restrict_top Q x) = restrict_top P x.
Proof.
  induction w as [P|P Q T a r l w ih].
  - have he : Sub (evaluation (word_nil F P)) (evaluation_allowed (word_nil F P)) =
        DPFusionSystem.arrow_identity F P.
    { apply val_inj. reflexivity. }
    rewrite he. exact (@pair_pull_id R (DPFusionOrbit.orbit_category F) M P
      (restrict_top P x)).
  - have he : Sub (evaluation (word_cons r w)) (evaluation_allowed (word_cons r w)) =
        DPFusionSystem.arrow_compose (Sub (step_map r) (step_allowed r))
          (Sub (evaluation w) (evaluation_allowed w)).
    { apply val_inj. reflexivity. }
    rewrite he raw_pull_composition ih. exact (centric_invariant_step hx r).
Qed.

Theorem centric_invariant_stable (p : nat) (pS : p.-group [set: S])
    (sat : DPFusionSaturation.saturated F p) (x : pair_value M [set: S]%G) :
    centric_invariant x -> stable_element x.
Proof.
  intros hx P Q f onto.
  destruct (DPFusionAlperinTheorem.centric_factorization_iso pS sat (valP f) onto)
    as [l [w hw]].
  have e : Sub (evaluation w) (evaluation_allowed w) = f.
  { apply val_inj. exact hw. }
  rewrite -e. exact (centric_invariant_word hx w).
Qed.

End Stable.
End DPFusionStable.
