From mathcomp Require Import all_ssreflect all_fingroup generic_quotient.
From DiazPark Require Import Category CategoryFinite CategoryFinitePullbacks FusionMaps
  FusionSystems FusionOrbit FusionFiniteCategory FusionMackeyShape MackeyStructures
  FusionCentricPullbackFactors FusionCentricPullbackUniqueness.
Import DPFusion DPFusionOrbit DPFusionMackey DPFusionCentricPullbackFactors DPFusionCentricPullbackUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricPullbacks.
Section Pullbacks.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Lemma representative_class (A B : {group S}) (h : orbit_hom F A B) : orbit_class (repr h) = h.
Proof. exact: reprK. Qed.
Variables P Q T : fc_object C.
Variables (f : fc_hom C P T) (g : fc_hom C Q T).

Definition retained_index :=
  {i : raw_index (repr f) (repr g) |
    DPFusionSystem.centric F (raw_apex (repr f) (repr g) (double_coset_representative i))}.
Definition retained_apex (i : retained_index) : fc_object C :=
  Sub (raw_apex (repr f) (repr g) (double_coset_representative (val i))) (valP i).
Definition retained_left (i : retained_index) : fc_hom C (retained_apex i) P :=
  orbit_class (raw_left (repr f) (repr g) (double_coset_representative (val i))).
Definition retained_right (i : retained_index) : fc_hom C (retained_apex i) Q :=
  orbit_class (raw_right (repr f) (repr g) (double_coset_representative (val i))).

Lemma retained_commutes i : fc_compose (retained_left i) f = fc_compose (retained_right i) g.
Proof.
have H : orbit_compose (retained_left i) (orbit_class (repr f)) =
    orbit_compose (retained_right i) (orbit_class (repr g)).
  exact (@raw_span_commutes S F (val P) (val Q) (val T) (repr f) (repr g)
    (double_coset_representative (val i)) (double_coset_representative_mem (val i))).
by rewrite !representative_class in H.
Qed.

Lemma retained_exists (X : fc_object C) (a : fc_hom C X P) (b : fc_hom C X Q) :
    fc_compose a f = fc_compose b g ->
    exists t : {i : retained_index & fc_hom C X (retained_apex i)},
      fc_compose (projT2 t) (retained_left (projT1 t)) = a /\
      fc_compose (projT2 t) (retained_right (projT1 t)) = b.
Proof.
move=> he.
have he' : orbit_compose (orbit_class (repr a)) (orbit_class (repr f)) =
    orbit_compose (orbit_class (repr b)) (orbit_class (repr g)).
  by rewrite !representative_class.
have [i [h [hl hr]]] := canonical_factor_exists he'.
have ci := @factor_apex_centric S F (val P) (val Q) (val T) (val X)
  (repr f) (repr g) (double_coset_representative i) h (valP X).
pose j : retained_index := Sub i ci.
exists (existT (fun j => fc_hom C X (retained_apex j)) j (orbit_class h)).
split.
- change (orbit_compose (orbit_class h) (orbit_class (raw_left (repr f) (repr g) (double_coset_representative i))) = a).
  exact (eq_trans hl (reprK a)).
- change (orbit_compose (orbit_class h) (orbit_class (raw_right (repr f) (repr g) (double_coset_representative i))) = b).
  exact (eq_trans hr (reprK b)).
Qed.

Lemma retained_unique (X : fc_object C)
    (t u : {i : retained_index & fc_hom C X (retained_apex i)}) :
    fc_compose (projT2 t) (retained_left (projT1 t)) =
      fc_compose (projT2 u) (retained_left (projT1 u)) ->
    fc_compose (projT2 t) (retained_right (projT1 t)) =
      fc_compose (projT2 u) (retained_right (projT1 u)) -> t = u.
Proof.
case: t=> i h; case: u=> j k; move=> he ke.
have he' : orbit_compose (orbit_class (repr h))
    (orbit_class (raw_left (repr f) (repr g) (double_coset_representative (val i)))) =
  orbit_compose (orbit_class (repr k))
    (orbit_class (raw_left (repr f) (repr g) (double_coset_representative (val j)))).
  by rewrite !representative_class.
have ke' : orbit_compose (orbit_class (repr h))
    (orbit_class (raw_right (repr f) (repr g) (double_coset_representative (val i)))) =
  orbit_compose (orbit_class (repr k))
    (orbit_class (raw_right (repr f) (repr g) (double_coset_representative (val j)))).
  by rewrite !representative_class.
have hd := raw_factor_double_coset he' ke' (valP X).
have hij : i = j.
  apply: val_inj; apply: val_inj.
  exact (eq_trans (esym (double_coset_representative_set (val i)))
    (eq_trans (esym hd) (double_coset_representative_set (val j)))).
destruct hij.
have hk := raw_same_representative_unique (valP X) he' ke'.
have hk' : h = k := eq_trans (esym (reprK h)) (eq_trans hk (reprK k)).
by rewrite hk'.
Qed.

Definition centric_pullback : @finite_pullback_decomposition (fc_category C) P Q T f g :=
  @Build_finite_pullback_decomposition (fc_category C) P Q T f g
    [the finType of retained_index] retained_apex retained_left retained_right
    retained_commutes retained_exists retained_unique.

End Pullbacks.
End DPFusionCentricPullbacks.
