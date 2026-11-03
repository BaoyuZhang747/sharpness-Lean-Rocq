From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient.
From DiazPark Require Import Category FusionMaps FusionSystems FusionOrbit FusionOrbitRanks
  FusionOuterOrbit FusionMackeyShape FusionMackeyRepresentatives MackeyPair MackeyPairSpanIso
  MackeyFusionBridge FusionQuotientMaps FusionQuotientConstruction FusionQuotientAutomorphisms
  FusionQuotientOrbitMaps FusionQuotientDoubleCosets FusionMackeyQuotientPair.
Import DPFusion DPFusionOrbit DPFusionRanks DPFusionOuterOrbit DPFusionMackey
  DPMackeyRepresentatives DPMackeyFusion DPFusionQuotientConstruction
  DPFusionQuotientAutomorphisms DPFusionQuotientOrbitMaps
  DPFusionQuotientDoubleCosets DPFusionMackeyQuotientPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPFusionMackeyQuotientFormula.
Section Formula.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Hypothesis kernel_trivial : forall (P : {group coset_of Z}) a,
  a \in 'ker (automorphism_morphism cZ P) ->
  forall x : pair_value M (preimage P), pair_push M (aut_orbit F (preimage P) a) x = x.
Let qM := quotient_pair kernel_trivial.

Lemma preimage_sub (P Q : {group coset_of Z}) :
  P \subset Q -> preimage P \subset preimage Q.
Proof. exact: morphpreS. Qed.

Lemma induced_inclusion (P Q : {group coset_of Z}) (h : P \subset Q) :
  induced_arrow cZ (inclusion_arrow F (preimage_sub h)) =
  inclusion_arrow (system cZ) h.
Proof.
apply: DPFusionSystem.arrow_ext=> q Pq.
have Px := @repr_mem S F Z cZ P q Pq.
change (arrow_value (induced_arrow cZ (inclusion_arrow F (preimage_sub h))) q = DPFusion.inclusion h q).
rewrite -(coset_reprK q) induced_arrowE //.
change (coset Z (DPFusion.inclusion (preimage_sub h) (fingroup.repr q)) =
  DPFusion.inclusion h (coset Z (fingroup.repr q))).
by rewrite !inclusion_in ?coset_reprK.
Qed.

Lemma span_apex_equal (P Q : {group coset_of Z}) q :
  preimage (inclusion_apex P Q q) =
  inclusion_apex (preimage P) (preimage Q) (fingroup.repr q).
Proof. by rewrite -{1}(coset_reprK q) (preimage_apex cZ). Qed.

Lemma span_apex_sub (P Q : {group coset_of Z}) q :
  preimage (inclusion_apex P Q q) \subset
  inclusion_apex (preimage P) (preimage Q) (fingroup.repr q).
Proof. by rewrite span_apex_equal. Qed.

Definition span_iso (P Q : {group coset_of Z}) q :=
  raw_onto_iso (raw_equal_rank_image (inclusion_arrow F (span_apex_sub P Q q))
    (congr1 (fun A : {group S} => #|A|) (span_apex_equal P Q q))).

Definition lifted_left (P Q : {group coset_of Z}) q :=
  DPFusionSystem.arrow_compose (inclusion_arrow F (span_apex_sub P Q q))
    (inclusion_left F (preimage P) (preimage Q) (fingroup.repr q)).
Definition lifted_right (P Q : {group coset_of Z}) q :=
  DPFusionSystem.arrow_compose (inclusion_arrow F (span_apex_sub P Q q))
    (inclusion_right F (preimage P) (preimage Q) (fingroup.repr q)).

Lemma lifted_left_value (P Q : {group coset_of Z}) q x :
  x \in preimage (inclusion_apex P Q q) -> val (lifted_left P Q q) x = x.
Proof.
move=> Ax; rewrite /lifted_left /DPFusionSystem.arrow_compose /= compose_in //.
rewrite /inclusion_arrow /inclusion_left /= !inclusion_in //.
exact: subsetP (span_apex_sub P Q q) x Ax.
Qed.
Lemma lifted_right_value (P Q : {group coset_of Z}) q x :
  x \in preimage (inclusion_apex P Q q) ->
  val (lifted_right P Q q) x = (x ^ (fingroup.repr q))%g.
Proof.
move=> Ax; rewrite /lifted_right /DPFusionSystem.arrow_compose /= compose_in //.
rewrite /inclusion_arrow /inclusion_right /= inclusion_in // conjugation_in //.
exact: subsetP (span_apex_sub P Q q) x Ax.
Qed.

Lemma induced_left (P Q : {group coset_of Z}) q :
  induced_arrow cZ (lifted_left P Q q) = inclusion_left (system cZ) P Q q.
Proof.
apply: DPFusionSystem.arrow_ext=> a Aa.
have Ax := @repr_mem S F Z cZ (inclusion_apex P Q q) a Aa.
change (arrow_value (induced_arrow cZ (lifted_left P Q q)) a = DPFusion.inclusion (inclusion_apex_left P Q q) a).
rewrite -(coset_reprK a) induced_arrowE //.
change (coset Z (val (lifted_left P Q q) (fingroup.repr a)) =
  DPFusion.inclusion (inclusion_apex_left P Q q) (coset Z (fingroup.repr a))).
by rewrite lifted_left_value // inclusion_in ?coset_reprK.
Qed.
Lemma induced_right (P Q : {group coset_of Z}) q :
  induced_arrow cZ (lifted_right P Q q) = inclusion_right (system cZ) P Q q.
Proof.
apply: DPFusionSystem.arrow_ext=> a Aa.
have Ax := @repr_mem S F Z cZ (inclusion_apex P Q q) a Aa.
change (arrow_value (induced_arrow cZ (lifted_right P Q q)) a = DPFusion.conjugation (inclusion_apex_right P Q q) a).
rewrite -(coset_reprK a) induced_arrowE //.
change (coset Z (val (lifted_right P Q q) (fingroup.repr a)) =
  DPFusion.conjugation (inclusion_apex_right P Q q) (coset Z (fingroup.repr a))).
rewrite lifted_right_value // conjugation_in ?coset_reprK //.
rewrite (morphJ (coset Z) (normZ_all cZ (fingroup.repr a)) (normZ_all cZ (fingroup.repr q))).
have ea : coset Z (fingroup.repr a) = a := coset_reprK a.
have eq : coset Z (fingroup.repr q) = q := coset_reprK q.
change ((coset Z (fingroup.repr a) ^ coset Z (fingroup.repr q))%g = (a ^ q)%g).
by rewrite ea eq.
Qed.

Lemma quotient_summand (P Q : {group coset_of Z}) q (x : pair_value qM P) :
  @inclusion_summand _ (system cZ) R qM P Q q x =
  @inclusion_summand S F R M (preimage P) (preimage Q) (fingroup.repr q) x.
Proof.
change (pair_push qM (orbit_class (inclusion_right (system cZ) P Q q))
  (pair_pull qM (orbit_class (inclusion_left (system cZ) P Q q)) x) =
  @inclusion_summand S F R M (preimage P) (preimage Q) (fingroup.repr q) x).
rewrite -induced_left -induced_right -!orbit_map_class.
rewrite /qM quotient_pair_pull quotient_pair_push.
apply: (@pair_span_iso_invariance R (orbit_category F) M _ _ (preimage P) (preimage Q)
  (span_iso P Q q) _ _ _ _ _ _ x).
- exact: orbit_compose_class.
- exact: orbit_compose_class.
Qed.

Theorem quotient_inclusion_mackey : inclusion_mackey_formula M ->
  inclusion_mackey_formula qM.
Proof.
move=> hM P Q T hP hQ x.
change (pair_pull qM (orbit_class (inclusion_arrow (system cZ) hQ))
  (pair_push qM (orbit_class (inclusion_arrow (system cZ) hP)) x) =
  \sum_(s : double_coset_index P Q T)
    @inclusion_summand _ (system cZ) R qM P Q (double_coset_representative s) x).
rewrite -!induced_inclusion -!orbit_map_class /qM quotient_pair_push quotient_pair_pull.
rewrite hM.
rewrite (bigop.reindex (@preimage_index S F Z cZ P Q T)
  (onW_bij _ (preimage_index_bijective cZ P Q T))) /=.
apply: eq_bigr=> i _.
change (@inclusion_summand S F R M (preimage P) (preimage Q)
  (double_coset_representative (preimage_index cZ i)) x =
  @inclusion_summand _ (system cZ) R qM P Q (double_coset_representative i) x).
rewrite quotient_summand.
exact: (@same_double_coset_summand S F R M (preimage P) (preimage Q) _ _
  (preimage_representative cZ i) x).
Qed.

Definition quotient_full_mackey (hM : inclusion_mackey_formula M) :=
  full_mackey_of_inclusions (quotient_inclusion_mackey hM).
End Formula.
End DPFusionMackeyQuotientFormula.
