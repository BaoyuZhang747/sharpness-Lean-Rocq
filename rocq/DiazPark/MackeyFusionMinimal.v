From mathcomp Require Import all_boot all_algebra all_fingroup boolp generic_quotient.
From DiazPark Require Import Category ModuleInfrastructure MackeyStructures MackeyGenerated
  MackeyMinimal FusionMaps FusionSystems FusionConjugacy FusionOrbit FusionMackeyShape
  FusionOrbitRanks MackeyFusionBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope quotient_scope.
Local Open Scope ring_scope.

Module DPMackeyMinimal.
Section FusionMinimal.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable R : comPzRingType.
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).

Definition subgroup_minimal (P : {group S}) :=
  (exists x : mackey_value M P, x <> 0) /\
  forall L : {group S}, L \proper P -> forall x : mackey_value M L, x = 0.

Lemma least_nonzero_exists : mackey_nonzero M ->
    exists Q : {group S}, mackey_least_nonzero M (fun P : {group S} => #|P|) Q.
Proof.
move=> [P [x hx]].
pose nonzero U := asbool (exists y : mackey_value M U, y <> 0).
have hP : nonzero P by apply/asboolP; exists x.
case: (@arg_minnP [the finType of {group S}] P nonzero (fun U => #|U|) hP)
  => Q hQ hmin.
exists Q; split; first by move/asboolP: hQ.
move=> U hlt y; case: (pselect (y = 0)) => // hy.
have hU : nonzero U by apply/asboolP; exists y.
have hle := hmin U hU.
by move: hle; rewrite leqNgt hlt.
Qed.

Lemma equal_rank_iso_exists P Q (f : DPFusionOrbit.orbit_hom F P Q) :
    #|P| = #|Q| -> exists e : @isomorphism (DPFusionOrbit.orbit_category F) P Q,
      iso_hom e = f.
Proof.
move=> h; exists (DPFusionRanks.orbit_equal_rank_iso f h).
exact: DPFusionRanks.orbit_equal_rank_iso_hom.
Qed.

Lemma conjugate_nonzero P Q : DPFusionSystem.conjugate F P Q ->
    (exists x : mackey_value M P, x <> 0) ->
    exists x : mackey_value M Q, x <> 0.
Proof.
move=> /existsP[f /andP[hf /eqP ho]].
exact: mackey_nonzero_transport
  (@DPFusionRanks.raw_onto_iso S F P Q (Sub f hf) ho).
Qed.

Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero M (fun P : {group S} => #|P|) Q.

Lemma conjugate_minimal P : DPFusionSystem.conjugate F Q P -> subgroup_minimal P.
Proof.
move=> hc; split; first exact: conjugate_nonzero hc leastQ.1.
move=> L hL x; apply: leastQ.2.
rewrite (DPFusionConjugacy.conjugate_card hc).
exact: proper_card hL.
Qed.

Lemma transfer_generation (hM : mackey_simple M) P x :
    module_span (fun y : mackey_value M P =>
      exists f : DPFusionOrbit.orbit_hom F Q P,
      exists v : mackey_value M Q, mackey_push M f v = y) x.
Proof.
exact: (@simple_minimal_transfer_generation R (DPFusionOrbit.orbit_category F)
  (DPFusionMackey.fusion_mackey_shape F) M (fun P : {group S} => #|P|)
  (@DPFusionRanks.orbit_rank_le S F) equal_rank_iso_exists Q leastQ hM P x).
Qed.

Lemma nonzero_support_arrow (hM : mackey_simple M) P :
    (exists x : mackey_value M P, x <> 0) ->
    exists f : DPFusionOrbit.orbit_hom F Q P, True.
Proof.
exact: (@simple_minimal_support_arrow R (DPFusionOrbit.orbit_category F)
  (DPFusionMackey.fusion_mackey_shape F) M (fun P : {group S} => #|P|)
  (@DPFusionRanks.orbit_rank_le S F) equal_rank_iso_exists Q leastQ hM P).
Qed.

Lemma orbit_image_conjugate P (f : DPFusionOrbit.orbit_hom F Q P) :
    DPFusionSystem.conjugate F Q (DPFusion.image (val (repr f))).
Proof.
apply: (DPFusionRanks.orbit_equal_rank_conjugate
  (iso_hom (DPFusionMackey.orbit_image_iso (repr f)))).
symmetry; exact: DPFusionConjugacy.map_image_card.
Qed.

Definition inclusion_transfer_generator P (y : mackey_value M P) :=
  exists L : {group S}, exists hLP : L \subset P,
    DPFusionSystem.conjugate F Q L /\
    exists v : mackey_value M L,
      mackey_push M (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_arrow F hLP)) v = y.

Theorem inclusion_transfer_generation (hM : mackey_simple M) P x :
    module_span (@inclusion_transfer_generator P) x.
Proof.
apply: (@span_mono R (mackey_value M P)
  (fun y => exists f : DPFusionOrbit.orbit_hom F Q P,
    exists v : mackey_value M Q, mackey_push M f v = y)) _ (transfer_generation hM x).
move=> y [f [v <-]]; exists (DPFusion.image (val (repr f))),
  (DPFusion.image_sub (val (repr f))); split; first exact: orbit_image_conjugate.
exists (mackey_push M (iso_hom (DPFusionMackey.orbit_image_iso (repr f))) v).
rewrite -mackey_push_comp DPFusionMackey.orbit_image_factorization.
by rewrite /DPFusionOrbit.orbit_class reprK.
Qed.

Theorem inclusion_restriction_detection (hM : mackey_simple M) P
    (x : mackey_value M P) :
    (forall (L : {group S}) (hLP : L \subset P), DPFusionSystem.conjugate F Q L ->
      mackey_pull M (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_arrow F hLP)) x = 0) ->
    x = 0.
Proof.
move=> hx.
apply: (@simple_minimal_restriction_detection R (DPFusionOrbit.orbit_category F)
  (DPFusionMackey.fusion_mackey_shape F) M (fun P : {group S} => #|P|)
  (@DPFusionRanks.orbit_rank_le S F) equal_rank_iso_exists Q leastQ hM P x).
move=> f.
have hf : DPFusionOrbit.orbit_class (repr f) = f := reprK f.
rewrite -hf -DPFusionMackey.orbit_image_factorization mackey_pull_comp.
rewrite (hx _ _ (orbit_image_conjugate f)); exact: linear0.
Qed.

Theorem inclusion_restriction_injective (hM : mackey_simple M) P
    (x y : mackey_value M P) :
    (forall (L : {group S}) (hLP : L \subset P), DPFusionSystem.conjugate F Q L ->
      mackey_pull M (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_arrow F hLP)) x =
      mackey_pull M (DPFusionOrbit.orbit_class (DPFusionMackey.inclusion_arrow F hLP)) y) ->
    x = y.
Proof.
move=> h; apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: (@inclusion_restriction_detection hM P (x-y)) => L hLP hc.
by rewrite linearB (h L hLP hc) subrr.
Qed.

Lemma minimal_conjugate (hM : mackey_simple M) P :
    subgroup_minimal P -> DPFusionSystem.conjugate F Q P.
Proof.
move=> [hn hz]; have [f _] := nonzero_support_arrow hM hn.
pose L := DPFusion.image (val (repr f)).
have hLnonzero : exists x : mackey_value M L, x <> 0.
  exact: mackey_nonzero_transport (DPFusionMackey.orbit_image_iso (repr f)) leastQ.1.
have hLP : ~~ (L \proper P).
  apply/negP=> hp; have [x hx] := hLnonzero; exact: hx (hz L hp x).
have hcard : (#|P| <= #|L|)%N.
  move: hLP; rewrite properEcard /L DPFusion.image_sub /= -leqNgt; exact.
have hQP : #|Q| = #|P|.
  apply/eqP; rewrite eqn_leq; apply/andP; split.
  - exact: DPFusionRanks.orbit_rank_le f.
  - move: hcard; by rewrite /L DPFusionConjugacy.map_image_card.
exact: DPFusionRanks.orbit_equal_rank_conjugate f hQP.
Qed.

(** Exact equality of the inclusion-minimal support with the actual fusion
    conjugacy class. No field, characteristic, saturation or dimension
    hypothesis is needed for this part of the manuscript lemma. *)
Theorem minimal_support_iff_conjugate (hM : mackey_simple M) P :
    subgroup_minimal P <-> DPFusionSystem.conjugate F Q P.
Proof. split; [exact: (@minimal_conjugate hM P) | exact: (@conjugate_minimal P)]. Qed.

Lemma conjugate_least_nonzero P : DPFusionSystem.conjugate F Q P ->
    mackey_least_nonzero M (fun U : {group S} => #|U|) P.
Proof.
move=> hc; split; first exact: conjugate_nonzero hc leastQ.1.
move=> U hU x; apply: leastQ.2.
by rewrite (DPFusionConjugacy.conjugate_card hc).
Qed.

Theorem conjugate_automorphism_simple (hM : mackey_simple M) P :
    DPFusionSystem.conjugate F Q P -> automorphism_simple_at M P.
Proof.
move=> hc.
exact: (@simple_minimal_automorphism_simple R (DPFusionOrbit.orbit_category F)
  (DPFusionMackey.fusion_mackey_shape F) M (fun U : {group S} => #|U|)
  (@DPFusionRanks.orbit_rank_le S F) equal_rank_iso_exists P
  (conjugate_least_nonzero hc) hM).
Qed.

End FusionMinimal.
End DPMackeyMinimal.



