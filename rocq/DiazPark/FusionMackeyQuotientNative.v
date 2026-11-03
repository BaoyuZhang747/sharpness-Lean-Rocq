From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient pgroup boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  FusionMaps FusionSystems FusionOrbit FusionSaturation FusionMackeyShape
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge MackeyBarReduction
  FusionMackeyFullBridge FusionQuotientMaps FusionQuotientConstruction
  FusionQuotientCollection FusionMackeyQuotientVanishing FusionMackeyQuotientDescent
  FusionMackeyQuotientCoefficients.
Import DPFusionOrbit DPFusionMackey DPMackeyFusion DPFusionMackeyFullBridge
  DPFusionQuotientConstruction DPFusionMackeyQuotientDescent DPFusionMackeyQuotientCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionMackeyQuotientNative.

Lemma native_codiagram_pair (R : comPzRingType) (C D : category)
    (B : mackey_shape C) (L : functor D C) (M : mackey_module R B) :
  mackey_codiagram L M = functor_comp (functor_op L) (pair_codiagram (pair_of_mackey M)).
Proof.
rewrite /mackey_codiagram /functor_comp /functor_op /pair_codiagram /pair_of_mackey.
f_equal; apply Prop_irrelevance.
Qed.

Lemma restricted_pair_codiagram (R : comPzRingType) (C D : category)
    (L : functor D C) (M : mackey_pair R C) :
  pair_codiagram (pair_restrict M L) = functor_comp (functor_op L) (pair_codiagram M).
Proof.
rewrite /pair_codiagram /pair_restrict /functor_comp /functor_op.
f_equal; apply Prop_irrelevance.
Qed.

Section Native.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Variable K : fieldType.
Variable M : mackey_module K (fusion_mackey_shape F).
Hypothesis simple : mackey_simple M.
Variable Q : {group S}.
Hypothesis leastQ : mackey_least_nonzero M (fun A : {group S} => #|A|) Q.
Variable p : nat.
Hypothesis charp : p \in [pchar K].
Hypothesis pS : p.-group [set: S].

Lemma native_pair_simple :
  mackey_simple (full_mackey_of_inclusions (@full_inclusion_mackey S F K M)).
Proof. by rewrite full_inclusion_roundtrip. Qed.
Lemma native_pair_least :
  mackey_least_nonzero (full_mackey_of_inclusions (@full_inclusion_mackey S F K M))
    (fun A : {group S} => #|A|) Q.
Proof. by rewrite full_inclusion_roundtrip. Qed.

Theorem native_missing_center_zero (hZ : ~~ (Z \subset Q))
    (P : {group S}) (hP : DPFusionSystem.centric F P) :
  forall x : mackey_value M P, x = 0.
Proof.
have charp0 : p%:R = (0 : K) := GRing.pcharf0 charp.
exact: (@DPFusionMackeyQuotientVanishing.centric_value_zero S F Z cZ K
  (pair_of_mackey M) (@full_inclusion_mackey S F K M) native_pair_simple Q native_pair_least
  hZ p charp0 pS P hP).
Qed.

Hypothesis sZQ : Z \subset Q.
Let pZ : p.-group Z := pgroupS (subsetT Z) pS.

Definition native_quotient_pair :=
  @simple_quotient_pair S F Z cZ K (pair_of_mackey M) (@full_inclusion_mackey S F K M)
    native_pair_simple Q native_pair_least p charp pZ sZQ.

Definition native_quotient : mackey_module K (fusion_mackey_shape (system cZ)) :=
  @simple_quotient S F Z cZ K (pair_of_mackey M) (@full_inclusion_mackey S F K M)
    native_pair_simple Q native_pair_least p charp pZ sZQ.

Theorem native_quotient_value P : mackey_value native_quotient P = mackey_value M (preimage P).
Proof. reflexivity. Qed.

Hypothesis sat : DPFusionSaturation.saturated F p.

Theorem native_collection_coefficient_equality :
  functor_comp
    (functor_op (DPFusionQuotientCollection.collection_quotient_functor cZ pZ sat))
    (mackey_codiagram (centric_inclusion (system cZ)) native_quotient) =
  mackey_codiagram (collection_inclusion cZ) M.
Proof.
rewrite !native_codiagram_pair.
have he := @collection_coefficient_equality S F Z cZ K (pair_of_mackey M)
  (@descent_kernel_trivial S F Z cZ K (pair_of_mackey M) (@full_inclusion_mackey S F K M)
    native_pair_simple Q native_pair_least p charp pZ sZQ) p pZ sat.
rewrite restricted_pair_codiagram in he.
exact he.
Qed.

Definition native_collection_coefficient_iso := functor_equality_iso native_collection_coefficient_equality.
End Native.
End DPFusionMackeyQuotientNative.

Print Assumptions DPFusionMackeyQuotientNative.native_missing_center_zero.
Print Assumptions DPFusionMackeyQuotientNative.native_quotient.
Print Assumptions DPFusionMackeyQuotientNative.native_collection_coefficient_iso.
