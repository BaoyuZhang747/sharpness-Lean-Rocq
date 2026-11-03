(** Central-quotient sharpness descent, using the actual quotient Mackey
    module, literal collection comparison and independently derived limits. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryIsomorphismAdjunction
  CategoryAdjunction CategoryNaturalIso CategoryModules CategoryDerivedLimits CategoryDerivedAdjunction
  CategoryDerivedZero CategoryAtomicDeletionTheorem BarHigherLimitVanishing
  FusionSystems FusionOrbit FusionSaturation FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientCollection FusionMackeyQuotientDescent FusionMackeyQuotientCoefficients
  FusionMackeyQuotientVanishing FusionCollectionRestrictionAdapter FusionSharpnessStatement
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge MackeyBarReduction
  MackeyDiagramIdentities MackeyFusionMinimal MackeyHigherLimitReduction FusionMackeyFullBridge.
Import GRing.Theory DPFusionOrbit DiazParkBarHigherLimitVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionCentralQuotientSharpness.
Section Descent.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable K : fieldType.
Hypothesis charp : p \in [pchar K].
Hypothesis quotient_sharp : DPFusionSharpness.sharpness K (DPFusionQuotientConstruction.system cZ).
Let pZ : p.-group Z := pgroupS (subsetT Z) pS.
Local Notation X := (DPFusionQuotientCollection.collection_category cZ).
Local Notation QF := (DPFusionQuotientConstruction.system cZ).

Variable M : mackey_pair K (orbit_category F).
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.
Let full := DPMackeyFusion.full_mackey_of_inclusions hM.
Hypothesis simple : mackey_simple full.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero full (fun A : {group S} => #|A|) Q.
Local Notation D := (pair_codiagram (pair_restrict M (centric_inclusion F))).
Local Notation DX := (functor_comp
  (functor_op (DPFusionMackeyQuotientCoefficients.collection_inclusion cZ)) (pair_codiagram M)).

Lemma literal_pair_restriction : DPFusionCollectionAdapter.literal_restriction cZ D = DX.
Proof.
apply (@functor_extensionality (opposite X) (module_category K)
  (DPFusionCollectionAdapter.literal_restriction cZ D) DX (Logic.eq_refl _)).
reflexivity.
Qed.

Lemma containing_simple_collection_zero (sZQ : Z \subset Q) : derived_positive_zero DX.
Proof.
  pose qM := DPFusionMackeyQuotientDescent.simple_quotient cZ simple leastQ charp pZ sZQ.
  have hq : forall n (q : derived_limit K (mackey_codiagram (centric_inclusion QF) qM) n.+1), q = 0 :=
    @quotient_sharp qM.
  rewrite /qM /DPFusionMackeyQuotientDescent.simple_quotient
    /DPMackeyFusion.full_mackey_of_inclusions of_pair_codiagram in hq.
  move=> n.
  pose qD := pair_codiagram (pair_restrict
    (DPFusionMackeyQuotientDescent.simple_quotient_pair cZ simple leastQ charp pZ sZQ)
    (centric_inclusion QF)).
  pose e := nat_iso_component
    (derived_left_adjoint_nat_iso K
      (adjunction_op (category_iso_adjunction (category_iso_symm
        (DPFusionQuotientCollection.collection_category_isomorphism cZ pZ sat)))) n.+1) qD.
  have hz : forall v : derived_limit K
    (functor_comp (functor_op
      (DPFusionQuotientCollection.collection_quotient_functor cZ pZ sat)) qD) n.+1, v = 0.
    apply (proj1 (module_iso_zero_iff e)). exact (hq n).
  pose ec := DPFusionMackeyQuotientDescent.simple_quotient_collection_iso
    cZ simple leastQ charp pZ sZQ sat.
  exact (proj1 (module_iso_zero_iff
    (functor_iso (derived_limit_functor K (opposite X) n.+1) ec)) hz).
Qed.

Theorem paired_simple_central_quotient_sharpness : derived_positive_zero D.
Proof.
  case: (boolP (Z \subset Q)) => [sZQ|missingZ].
  - apply (proj2 (DPFusionCollectionAdapter.literal_collection_acyclic_iff cZ pS pZ sat D)).
    rewrite literal_pair_restriction. exact: containing_simple_collection_zero.
  - move=> n. apply (@pointwise_zero_derived_limits K (centric_orbit_category F) D).
    move=> P v. exact (@DPFusionMackeyQuotientVanishing.centric_value_zero S F Z cZ K M hM
      simple Q leastQ missingZ p (pcharf0 charp) pS (val P) (valP P) v).
Qed.
End Descent.

Theorem central_quotient_sharpness (S : finGroupType) (F : DPFusionSystem.system S)
    (Z : {group S}) (cZ : DPFusionQuotient.central F Z) (p : nat)
    (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (K : fieldType) (charp : p \in [pchar K])
    (quotient_sharp : DPFusionSharpness.sharpness K (DPFusionQuotientConstruction.system cZ)) :
    DPFusionSharpness.sharpness K F.
Proof.
  move=> M. apply (@DPMackeyHigherReduction.simple_to_arbitrary_centric_higher_limits S F K) => N simpleN.
  have [Q leastQ] := DPMackeyMinimal.least_nonzero_exists simpleN.1.
  have simpleP : mackey_simple (DPMackeyFusion.full_mackey_of_inclusions
      (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N)).
    by rewrite DPFusionMackeyFullBridge.full_inclusion_roundtrip.
  have leastP : mackey_least_nonzero (DPMackeyFusion.full_mackey_of_inclusions
      (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N)) (fun A : {group S} => #|A|) Q.
    by rewrite DPFusionMackeyFullBridge.full_inclusion_roundtrip.
  rewrite /DPMackeyHigherReduction.centric_higher_acyclic native_pair_codiagram.
  exact (@paired_simple_central_quotient_sharpness S F Z cZ p pS sat K charp quotient_sharp
    (pair_of_mackey N) (@DPFusionMackeyFullBridge.full_inclusion_mackey S F K N) simpleP Q leastP).
Qed.
End DPFusionCentralQuotientSharpness.
