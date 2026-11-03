(** Actual centric acyclicity: all geometric and arithmetic inputs of the
    integral Burnside argument are instantiated by their proved fusion
    category constructions. Coefficient modules are unrestricted. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup generic_quotient boolp.
From DiazPark Require Import Category CategoryFinite CategoryFinitePullbacks CategoryModules
  CategoryDerivedLimits FusionMaps FusionSystems FusionOrbit FusionSaturation FusionMackeyShape
  FusionFiniteCategory FusionCentricBasics FusionCentricProducts FusionCentricPullbacks
  FusionCentricHomCount FusionAlperinInductionTools FusionCentricMackey
  MackeyStructures MackeyMinimal MackeyPair MackeyPairDiagrams MackeyFusionBridge MackeyFusionMinimal
  MackeyBarReduction FusionMackeyFullBridge BurnsideDerivedAcyclicity
  PrimeLocalRing PrimeLocalUniversal.
Import GRing.Theory DPFusionSystem DPFusionOrbit DPMackeyFusion DPPrimeLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Module DPFusionCentricAcyclicity.
Section Supported.
Variable S : finGroupType.
Variable F : system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : comPzRingType.
Variable phi : {rmorphism DPPrimeLocal.type p -> R}.
Variable M : mackey_pair R (orbit_category F).
Hypothesis hM : inclusion_mackey_formula M.
Hypothesis supported : forall P : {group S}, ~~ centric F P ->
  forall x : pair_value M P, x=0.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Let N := pair_restrict M (centric_inclusion F).
Definition top_object : fc_object C :=
  Sub [set: S]%G (DPFusionAlperinInductionTools.centric_top F).

Lemma supported_pullback_formula (A B T : fc_object C)
    (f : fc_hom C A T) (g : fc_hom C B T) (x : pair_value N A) :
    pair_pull N g (pair_push N f x) =
    \sum_(i : pb_index (DPFusionCentricPullbacks.centric_pullback f g))
      pair_push N (pb_right (DPFusionCentricPullbacks.centric_pullback f g) i)
        (pair_pull N (pb_left (DPFusionCentricPullbacks.centric_pullback f g) i) x).
Proof.
have he := @DPFusionCentricMackey.raw_centric_mackey_formula S F R M hM supported
  (val A) (val B) (val T) (repr f) (repr g) x.
rewrite /orbit_class !reprK in he.
exact he.
Qed.

Theorem supported_centric_higher_limits_zero n :
    forall q : derived_limit R (pair_codiagram N) n.+1, q=0.
Proof.
apply: (@centric_mackey_positive_derived_zero S F top_object
  (DPFusionCentricProducts.centric_product pS sat top_object)
  (@DPFusionCentricPullbacks.centric_pullback S F)
  p hp _ R phi N supported_pullback_formula n).
move=> X.
have h := @DPFusionCentricHomCount.top_hom_coprime S F p hp pS sat (val X) (valP X).
rewrite cardsT in h; exact h.
Qed.
End Supported.

Section FullCoefficients.
Variable S : finGroupType.
Variable F : system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable R : comPzRingType.
Variable phi : {rmorphism DPPrimeLocal.type p -> R}.
Variable M : mackey_module R (DPFusionMackey.fusion_mackey_shape F).

Theorem full_supported_centric_higher_limits_zero
    (supported : forall P : {group S}, ~~ centric F P ->
      forall x : mackey_value M P, x=0) n :
    forall q : derived_limit R (mackey_codiagram (centric_inclusion F) M) n.+1, q=0.
Proof.
have he : mackey_codiagram (centric_inclusion F) M =
    pair_codiagram (pair_restrict (pair_of_mackey M) (centric_inclusion F)).
  rewrite /mackey_codiagram /pair_codiagram /pair_restrict /pair_of_mackey.
  f_equal; apply Prop_irrelevance.
rewrite he.
exact (@supported_centric_higher_limits_zero S F p hp pS sat R phi
  (pair_of_mackey M) (@DPFusionMackeyFullBridge.full_inclusion_mackey S F R M) supported n).
Qed.

Hypothesis simple : mackey_simple M.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero M (fun P : {group S} => #|P|) Q.
Hypothesis centricQ : centric F Q.

Lemma simple_centric_supported P : ~~ centric F P ->
    forall x : mackey_value M P, x=0.
Proof.
move=> hn x; case: (pselect (x=0))=> // hx.
have [f _] := @DPMackeyMinimal.nonzero_support_arrow S F R M Q leastQ simple P
  (ex_intro _ x hx).
have hc := DPFusionCentricBasics.centric_image (valP (repr f)) centricQ.
have hP := DPFusionCentricBasics.centric_overgroup (DPFusion.image_sub (val (repr f))) hc.
by move: hn; rewrite hP.
Qed.

Theorem simple_centric_higher_limits_zero n :
    forall q : derived_limit R (mackey_codiagram (centric_inclusion F) M) n.+1, q=0.
Proof. exact: full_supported_centric_higher_limits_zero simple_centric_supported n. Qed.
End FullCoefficients.

Section FieldCoefficients.
Variable S : finGroupType.
Variable F : system S.
Variable p : nat.
Variable K : fieldType.
Hypothesis charp : p \in [pchar K].

Lemma field_local : DPPrimeLocalUniversal.primes_inverted p [the comPzRingType of (K : Type)].
Proof.
move=> n hn; exists ((n%:R : K)^-1); apply: mulVr.
have hp := pcharf_prime charp.
by rewrite unitfE -(dvdn_pcharf charp) -prime_coprime.
Qed.

Theorem field_simple_centric_higher_limits_zero
    (pS : p.-group [set: S]) (sat : DPFusionSaturation.saturated F p)
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F))
    (simple : mackey_simple M) (Q : {group S})
    (leastQ : mackey_least_nonzero M (fun P : {group S} => #|P|) Q)
    (centricQ : centric F Q) n :
    forall q : derived_limit K (mackey_codiagram (centric_inclusion F) M) n.+1, q=0.
Proof.
exact: (@simple_centric_higher_limits_zero S F p (pcharf_prime charp) pS sat
  [the comPzRingType of (K : Type)] (DPPrimeLocalUniversal.canonical_map field_local)
  M simple Q leastQ centricQ n).
Qed.
End FieldCoefficients.
End DPFusionCentricAcyclicity.

Print Assumptions DPFusionCentricAcyclicity.supported_centric_higher_limits_zero.
Print Assumptions DPFusionCentricAcyclicity.field_simple_centric_higher_limits_zero.
