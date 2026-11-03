From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit
  FusionMackeyShape MackeyStructures MackeyPair.

(** The manuscript input is only the inclusion double-coset identity.
    The all-arrow identity is derived for actual fusion orbit morphisms. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPMackeyFusion.
Section FusionCoefficients.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).

Definition inclusion_mackey_formula :=
  forall (P Q T : {group S}) (hP : P \subset T) (hQ : Q \subset T) x,
    pair_pull M (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_arrow F hQ))
      (pair_push M (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_arrow F hP)) x) =
    \sum_(s : DPFusionMackey.double_coset_index P Q T)
      pair_push M (span_right (DPFusionMackey.inclusion_term F s))
        (pair_pull M (span_left (DPFusionMackey.inclusion_term F s)) x).

Hypothesis hM : inclusion_mackey_formula.

Lemma raw_mackey_formula (P Q T : {group S})
    (f : DPFusionSystem.arrow F P T) (g : DPFusionSystem.arrow F Q T) x :
    pair_pull M (DPFusionOrbit.orbit_class g)
      (pair_push M (DPFusionOrbit.orbit_class f) x) =
    \sum_(s : DPFusionMackey.raw_index f g)
      pair_push M (span_right (@DPFusionMackey.raw_term S F P Q T f g s))
        (pair_pull M (span_left (@DPFusionMackey.raw_term S F P Q T f g s)) x).
Proof.
have ht := @pair_mackey_iso_transport R (DPFusionOrbit.orbit_category F) M
  P Q (DPFusion.image (val f)) (DPFusion.image (val g)) T
  (DPFusionMackey.orbit_image_iso f) (DPFusionMackey.orbit_image_iso g)
  (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_arrow F (DPFusion.image_sub (val f))))
  (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_arrow F (DPFusion.image_sub (val g))))
  (DPFusionMackey.raw_index f g)
  (fun s => DPFusionMackey.inclusion_term F s)
  (@hM _ _ _ (DPFusion.image_sub (val f)) (DPFusion.image_sub (val g))) x.
rewrite !DPFusionMackey.orbit_image_factorization in ht.
rewrite ht; apply: eq_bigr => s _.
rewrite /DPFusionMackey.inclusion_term /DPFusionMackey.raw_term.
rewrite DPFusionMackey.raw_left_image_factorization
  DPFusionMackey.raw_right_image_factorization.
reflexivity.
Qed.

Lemma all_arrow_mackey_formula :
    pair_mackey_formula M (DPFusionMackey.fusion_mackey_shape F).
Proof.
move=> P Q T f g x.
have ht := raw_mackey_formula (repr f) (repr g) x.
rewrite /DPFusionOrbit.orbit_class !reprK in ht.
exact ht.
Qed.

Definition full_mackey_of_inclusions :
    mackey_module R (DPFusionMackey.fusion_mackey_shape F) :=
  mackey_module_of_pair (all_arrow_mackey_formula).

Lemma full_mackey_value P :
    mackey_value full_mackey_of_inclusions P = pair_value M P.
Proof. reflexivity. Qed.

Lemma full_mackey_pull P Q (f : hom (DPFusionOrbit.orbit_category F) P Q) x :
    mackey_pull full_mackey_of_inclusions f x = pair_pull M f x.
Proof. reflexivity. Qed.

Lemma full_mackey_push P Q (f : hom (DPFusionOrbit.orbit_category F) P Q) x :
    mackey_push full_mackey_of_inclusions f x = pair_push M f x.
Proof. reflexivity. Qed.

End FusionCoefficients.
End DPMackeyFusion.


