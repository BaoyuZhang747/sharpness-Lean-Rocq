From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOrbitRanks
  FusionCentralizerMaps FusionSubsystemOrbit FusionSubsystemRestriction
  FusionMackeyShape FusionMackeyRepresentatives FusionSubsystemDoubleCosets
  MackeyPair MackeyPairDiagrams MackeyPairSpanIso MackeyFusionBridge.
Import DPFusion DPFusionSystem DPFusionOrbit DPFusionRanks DPFusionSubgroup
  DPFusionSubsystem DPFusionSubsystemRestriction DPFusionMackey
  DPMackeyRepresentatives DPSubsystemDoubleCosets DPMackeyFusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPSubsystemMackey.
Section Restriction.
Variable S : finGroupType.
Variable F : system S.
Variable C : {group S}.
Local Notation U := [subg C]%type.
Variable H : system [the finGroupType of U].
Hypothesis hH : forall (P Q : {group U}) (f : DPFusion.map P Q),
  allowed H f -> allowed F (lift f).
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).

Lemma ambient_span_sub (P Q : {group U}) (t : U) :
    ambient (inclusion_apex P Q t) \subset inclusion_apex (ambient P) (ambient Q) (val t).
Proof. by rewrite ambient_apex. Qed.

Lemma ambient_span_rank (P Q : {group U}) (t : U) :
    #|ambient (inclusion_apex P Q t)| = #|inclusion_apex (ambient P) (ambient Q) (val t)|.
Proof. by rewrite ambient_apex. Qed.

Definition ambient_span_iso (P Q : {group U}) (t : U) :=
  raw_onto_iso (raw_equal_rank_image (inclusion_arrow F (ambient_span_sub P Q t))
    (ambient_span_rank P Q t)).

Lemma ambient_span_left (P Q : {group U}) (t : U) :
    Category.compose (iso_hom (ambient_span_iso P Q t))
      (orbit_class (inclusion_left F (ambient P) (ambient Q) (val t))) =
    orbit_class (ambient_arrow hH (inclusion_left H P Q t)).
Proof.
change (orbit_compose (orbit_class (inclusion_arrow F (ambient_span_sub P Q t)))
  (orbit_class (inclusion_left F (ambient P) (ambient Q) (val t))) =
  orbit_class (ambient_arrow hH (inclusion_left H P Q t))).
rewrite orbit_compose_class; apply: congr1; apply: arrow_ext=> x hx.
have hl := ambient_repr hx.
rewrite -(ambient_subgK hx).
change (DPFusion.compose (DPFusion.inclusion (ambient_span_sub P Q t))
  (val (inclusion_left F (ambient P) (ambient Q) (val t))) (val (subg C x)) =
  lift (val (inclusion_left H P Q t)) (val (subg C x))).
rewrite DPFusion.compose_in ?ambient_mem // DPFusion.inclusion_in ?ambient_mem //.
rewrite liftE // /inclusion_left /= !DPFusion.inclusion_in ?ambient_mem //.
exact: subsetP (ambient_span_sub P Q t) _ (ambient_mem hl).
Qed.

Lemma ambient_span_right (P Q : {group U}) (t : U) :
    Category.compose (iso_hom (ambient_span_iso P Q t))
      (orbit_class (inclusion_right F (ambient P) (ambient Q) (val t))) =
    orbit_class (ambient_arrow hH (inclusion_right H P Q t)).
Proof.
change (orbit_compose (orbit_class (inclusion_arrow F (ambient_span_sub P Q t)))
  (orbit_class (inclusion_right F (ambient P) (ambient Q) (val t))) =
  orbit_class (ambient_arrow hH (inclusion_right H P Q t))).
rewrite orbit_compose_class; apply: congr1; apply: arrow_ext=> x hx.
have hl := ambient_repr hx.
rewrite -(ambient_subgK hx).
change (DPFusion.compose (DPFusion.inclusion (ambient_span_sub P Q t))
  (val (inclusion_right F (ambient P) (ambient Q) (val t))) (val (subg C x)) =
  lift (val (inclusion_right H P Q t)) (val (subg C x))).
rewrite DPFusion.compose_in ?ambient_mem // DPFusion.inclusion_in ?ambient_mem //.
rewrite liftE // /inclusion_right /= !DPFusion.conjugation_in ?ambient_mem //.
exact: subsetP (ambient_span_sub P Q t) _ (ambient_mem hl).
Qed.

Lemma restricted_summand (P Q : {group U}) (t : U)
    (x : pair_value (restricted_pair hH M) P) :
    @inclusion_summand _ H R (restricted_pair hH M) P Q t x =
    @inclusion_summand S F R M (ambient P) (ambient Q) (val t) x.
Proof.
change (pair_push M (orbit_map hH (orbit_class (inclusion_right H P Q t)))
  (pair_pull M (orbit_map hH (orbit_class (inclusion_left H P Q t))) x) =
  @inclusion_summand S F R M (ambient P) (ambient Q) (val t) x).
rewrite !orbit_map_class.
exact: (@pair_span_iso_invariance R (orbit_category F) M _ _ (ambient P) (ambient Q)
  (ambient_span_iso P Q t) _ _ _ _ (ambient_span_left P Q t) (ambient_span_right P Q t) x).
Qed.

Theorem restricted_inclusion_mackey : inclusion_mackey_formula M ->
    inclusion_mackey_formula (restricted_pair hH M).
Proof.
move=> hM P Q T hP hQ x.
change (pair_pull M (orbit_map hH (orbit_class (inclusion_arrow H hQ)))
  (pair_push M (orbit_map hH (orbit_class (inclusion_arrow H hP))) x) =
  \sum_(s : double_coset_index P Q T)
  @inclusion_summand _ H R (restricted_pair hH M) P Q (double_coset_representative s) x).
rewrite !orbit_map_class !ambient_inclusion.
rewrite hM.
rewrite (bigop.reindex (@ambient_index S C P Q T) (onW_bij _ (ambient_index_bijective P Q T))) /=.
apply: eq_bigr=> i _.
change (@inclusion_summand S F R M (ambient P) (ambient Q)
  (double_coset_representative (ambient_index i)) x =
  @inclusion_summand _ H R (restricted_pair hH M) P Q (double_coset_representative i) x).
rewrite restricted_summand.
exact: (@same_double_coset_summand S F R M (ambient P) (ambient Q) _ _
  (ambient_representative i) x).
Qed.

Definition restricted_full_mackey (hM : inclusion_mackey_formula M) :=
  full_mackey_of_inclusions (restricted_inclusion_mackey hM).

End Restriction.
End DPSubsystemMackey.

Print Assumptions DPSubsystemMackey.restricted_inclusion_mackey.
Print Assumptions DPSubsystemMackey.restricted_full_mackey.




