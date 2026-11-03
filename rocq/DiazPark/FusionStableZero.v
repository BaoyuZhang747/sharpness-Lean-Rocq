(** Degree-zero vanishing for the restriction of an actual simple Mackey
    functor to a saturated subsystem whose centric subgroups remain centric. *)

From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  FusionMaps FusionSystems FusionOrbit FusionConjugacy FusionCentricBasics
  FusionSaturation FusionCentralizerMaps FusionSubsystemOrbit FusionSubsystemRestriction
  FusionStableElements FusionStableLimit MackeyStructures MackeyPair MackeyPairDiagrams
  MackeyFusionBridge MackeyFusionMinimal TraceGeneratedRestriction.
Import GRing.Theory DPFusion DPFusionSubgroup DPFusionSubsystemRestriction DPFusionStable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionStableZero.
Section Vanishing.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable C : {group S}.
Local Notation T := [subg C]%type.
Variable H : DPFusionSystem.system [the finGroupType of T].
Hypothesis hH : forall (P Q : {group T}) (f : DPFusion.map P Q),
  DPFusionSystem.allowed H f -> DPFusionSystem.allowed F (lift f).
Hypothesis hcentric : forall P : {group T},
  DPFusionSystem.centric H P -> DPFusionSystem.centric F (ambient P).
Variable R : comPzRingType.
Variable M : mackey_pair R (DPFusionOrbit.orbit_category F).
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.
Let full := DPMackeyFusion.full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Hypothesis Qnoncentric : ~~ DPFusionSystem.centric F Q.
Variable p : nat.
Hypothesis charp : p%:R = (0 : R).
Hypothesis pT : p.-group [set: T].
Let N := restricted_pair hH M.

Lemma minimal_local_not_centric (P : {group T}) :
    DPFusionSystem.conjugate F Q (ambient P) -> ~~ DPFusionSystem.centric H P.
Proof.
  intros hc. apply/negP. intro hp. apply (negP Qnoncentric).
  apply (DPFusionCentricBasics.centric_conjugate (DPFusionConjugacy.conjugate_reverse hc)).
  exact (hcentric hp).
Qed.

Theorem subsystem_stable_zero (x : pair_value N [set: T]%G) :
    @stable_element [the finGroupType of T] H R N x -> x = 0.
Proof.
  intro hx.
  apply (@DPMackeyMinimal.inclusion_restriction_detection S F R full Q leastQ simple
    (ambient [set: T]%G) x).
  intros L hL hQL.
  have hLC : L \subset C := subset_trans hL (ambient_sub [set: T]%G).
  destruct (ambient_subgroup_exists hLC) as [P he]. subst L.
  have hp := minimal_local_not_centric hQL.
  move/forallPn: hp => [P0 hp0].
  rewrite negb_imply in hp0. move/andP: hp0 => [hPP0 hn0].
  have hQ0 := DPFusionConjugacy.conjugate_trans hQL
    (DPFusionSubsystem.ambient_conjugate hH hPP0).
  have hpamb : p.-group (ambient [set: T]%G) := morphim_pgroup sgval pT.
  have hz : restrict_top N P0 x = 0.
  { rewrite /N restricted_top_formula.
    exact (@DPCentralizerRestriction.centralizer_restriction_zero S F R M hM simple
      Q leastQ (ambient P0) (ambient [set: T]%G) hQ0 (ambient_subset (subsetT P0))
      p charp hpamb (ambient_centralizer_witness hn0) x). }
  move/existsP: hPP0 => [f /andP[hf /eqP ho]].
  have hs := hx P P0 (Sub f hf) ho.
  rewrite hz /raw_pull linear0 in hs.
  have hzP : restrict_top N P x = 0 := esym hs.
  rewrite /N restricted_top_formula in hzP.
  have eh : hL = ambient_subset (subsetT P) := Prop_irrelevance _ _.
  rewrite eh. exact hzP.
Qed.

Hypothesis satH : DPFusionSaturation.saturated H p.

Theorem subsystem_centric_limit_zero
    (y : module_limit_type (DPFusionStableLimit.centric_coefficient N)) : y = 0.
Proof.
  apply module_limit_val_injective. apply functional_extensionality_dep. intros [P hP].
  have hs : @stable_element [the finGroupType of T] H R N
      (DPFusionStableLimit.limit_at_top N y) :=
    centric_invariant_stable pT satH (DPFusionStableLimit.limit_top_invariant y).
  have hz := subsystem_stable_zero hs.
  have hc := DPFusionStableLimit.limit_coordinate y hP.
  rewrite hz /restrict_top /raw_pull linear0 in hc.
  exact (esym hc).
Qed.

End Vanishing.
End DPFusionStableZero.
