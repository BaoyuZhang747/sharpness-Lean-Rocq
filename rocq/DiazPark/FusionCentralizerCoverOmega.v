From mathcomp Require Import all_ssreflect all_fingroup center abelian pgroup sylow generic_quotient.
From DiazPark Require Import Category CategoryAdjunction FusionMaps FusionSystems FusionOrbit
  FusionCentricBasics FusionCentricCriterion FusionCentralizerCover.
Import DPFusion DPFusionOrbit DPFusionCentralizerCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverOmega.
Section GroupFacts.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.

Lemma center_sub_image_center (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> DPFusionSystem.centric F P ->
  'Z(Q) \subset DPFusion.map_morphism f @* 'Z(P).
Proof.
move=> hf hc; apply/subsetP=> z /setIP[Qz Cz].
have CzI : z \in 'C(DPFusion.image f) := subsetP (centS (DPFusion.image_sub f)) z Cz.
have Iz := subsetP (DPFusionCentricCriterion.centric_self_centralizing
  (DPFusionCentricBasics.centric_image hf hc)) z CzI.
have /morphimP[x Px _ ez] := Iz.
change (z = f x) in ez.
have Zx : x \in 'Z(P).
  apply/setIP; split=> //; apply/centP=> y Py.
  apply: (DPFusion.map_injective (f := f) (groupM Px Py) (groupM Py Px)).
  rewrite !DPFusion.map_mul // -ez.
  exact: (centP Cz _ (DPFusion.map_into f Py)).
apply/morphimP; exists x=> //.
Qed.

Lemma omega_sub_image_omega (P Q : {group S}) (f : DPFusion.map P Q) :
  DPFusionSystem.allowed F f -> DPFusionSystem.centric F P ->
  'Ohm_1('Z(Q)) \subset DPFusion.map_morphism f @* 'Ohm_1('Z(P)).
Proof.
move=> hf hc.
rewrite (injm_Ohm _ (DPFusion.map_injm f) (center_sub P)).
exact (@OhmS 1 S 'Z(Q)%G (DPFusion.map_morphism f @* 'Z(P))%G (center_sub_image_center hf hc)).
Qed.

End GroupFacts.
Section SectionAdjunction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis ntS : [set: S] :!=: 1.
Local Notation CC := (centric_orbit_category F).
Local Notation Cov := (cover_category F p).

Lemma centric_nontrivial (P : centric_object F) : val P :!=: 1.
Proof.
apply/negP=> /eqP eP.
have h := DPFusionCentricCriterion.centric_self_centralizing (valP P).
rewrite eP cent1T in h.
have eS := trivgP h.
by move: ntS; rewrite eS eqxx.
Qed.

Lemma omega_nontrivial (P : centric_object F) : 'Ohm_1('Z(val P)) :!=: 1.
Proof.
rewrite Ohm1_eq1; apply/negP=> /eqP hz.
have pP : p.-group (val P) := pgroupS (subsetT _) pS.
have eP := trivg_center_pgroup pP hz.
by move: (centric_nontrivial P); rewrite eP eqxx.
Qed.

Definition section_object (P : centric_object F) : cover_object F p.
Proof.
exists (P, 'Ohm_1('Z(val P))%G); apply/and3P; split.
- exact: omega_nontrivial.
- apply: Ohm1_abelem; last exact: center_abelian.
  exact: pgroupS (subset_trans (center_sub _) (subsetT _)) pS.
- exact: Ohm_sub.
Defined.

Lemma elementary_sub_omega (X : cover_object F p) :
  elementary X \subset 'Ohm_1('Z(carrier X)).
Proof.
rewrite -(Ohm1_id (elementary_abelem X)).
exact (@OhmS 1 S (elementary X) 'Z(carrier X)%G (elementary_center X)).
Qed.

Lemma section_raw_condition (P : centric_object F) (X : cover_object F p)
    (f : DPFusionSystem.arrow F (val P) (carrier X)) :
  @raw_condition S F p (section_object P) X f.
Proof.
exact: subset_trans (elementary_sub_omega X)
  (omega_sub_image_omega (valP f) (valP P)).
Qed.

Lemma section_condition (P : centric_object F) (X : cover_object F p)
    (f : orbit_hom F (val P) (carrier X)) :
  @condition S F p (section_object P) X f.
Proof. exact: section_raw_condition. Qed.

Definition section_arrow (P Q : centric_object F) (f : hom CC P Q) :
  cover_hom (section_object P) (section_object Q) := Sub f (@section_condition P (section_object Q) f).

Definition section_functor : functor CC Cov.
Proof.
refine (@Build_functor CC Cov section_object (fun P Q f => section_arrow f) _ _).
- move=> P; apply: val_inj; by [].
- move=> P Q R f g; apply: val_inj; by [].
Defined.

Lemma section_forget_object (P : centric_object F) :
  fobj (forget F p) (fobj section_functor P) = P.
Proof. reflexivity. Qed.

Lemma section_forget_map (P Q : centric_object F) (f : hom CC P Q) :
  fmap (forget F p) (fmap section_functor f) = f.
Proof. reflexivity. Qed.

Definition section_unit : nat_trans (functor_id CC) (functor_comp section_functor (forget F p)).
Proof.
refine (@Build_nat_trans CC CC (functor_id CC) (functor_comp section_functor (forget F p))
  (fun P => @Category.identity CC P) _).
move=> P Q f; exact: eq_trans (compose_id_right f) (esym (compose_id_left f)).
Defined.

Definition section_counit_arrow (X : cover_object F p) :
  cover_hom (section_object (underlying X)) X :=
  Sub (orbit_identity F (carrier X)) (@section_condition (underlying X) X (orbit_identity F (carrier X))).

Definition section_counit : nat_trans (functor_comp (forget F p) section_functor) (functor_id Cov).
Proof.
refine (@Build_nat_trans Cov Cov (functor_comp (forget F p) section_functor) (functor_id Cov)
  section_counit_arrow _).
move=> X Y f; apply: val_inj.
exact: eq_trans (@Category.compose_id_right (orbit_category F) (carrier X) (carrier Y) (val f))
  (esym (@Category.compose_id_left (orbit_category F) (carrier X) (carrier Y) (val f))).
Defined.

Definition section_forget_adjunction : adjunction section_functor (forget F p).
Proof.
refine (@Build_adjunction CC Cov section_functor (forget F p) section_unit section_counit _ _).
- move=> P; apply: val_inj.
  exact: (@Category.compose_id_left (orbit_category F) (val P) (val P) (orbit_identity F (val P))).
- move=> X.
  exact: (@Category.compose_id_left (orbit_category F) (carrier X) (carrier X)
    (orbit_identity F (carrier X))).
Defined.

End SectionAdjunction.
End DPFusionCentralizerCoverOmega.





