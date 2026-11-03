(** Public algebraic statements for the supplied v1.6b manuscript.
    The field corollary below is deduced from the prime-local theorem
    through the actual all-degree scalar-restriction isomorphism. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp vector boolp.
From DiazPark Require Import Category CategoryIsomorphism CategoryReindex CategoryModules
  CategoryModuleLimits CategoryDerivedLimits ModuleInfrastructure
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionMackeyShape
  FusionQuotientMaps FusionQuotientConstruction FusionQuotientNormalization FusionQuotientOrbitMaps
  FusionQuotientCollection FusionCollectionRestrictionAdapter FusionCollectionDegreewise
  FusionCentricAcyclicity FusionSharpnessStatement FusionSharpnessCoefficients
  FusionCentralizerMaps FusionSubsystemRestriction FusionStableLimit FusionStableZero
  MackeyStructures MackeyPair MackeyPairDiagrams MackeyFusionBridge MackeyBarReduction
  MackeyFusionMinimal MackeyScalarRestriction PrimeLocalRing PrimeLocalUniversal.
From DiazParkV16b Require Import MackeyFixedDegreeClosure MackeyMinimalSupportManuscript
  MackeyNoncentricSimpleReduction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPFusionOrbit DPPrimeLocal.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPDiazParkManuscript.

(** This is actual finite-dimensionality of the existing value module:
    a finite-dimensional vector-space coordinate axiom, without changing
    its carrier or its linear operations. *)
Definition finite_dimensional_values (S : finGroupType) (F : DPFusionSystem.system S)
    (K : fieldType) (M : mackey_pair K (orbit_category F)) : Prop :=
  forall P : {group S}, exists d : nat, inhabited (Vector.axiom d (pair_value M P)).

Section MainTheorems.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Local Notation Zp := [the comPzRingType of (DPPrimeLocal.type p : Type)].

Theorem prime_local_main
    (M : mackey_pair Zp (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit Zp
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
rewrite -(DPMackeyFixedDegree.inclusion_centric_codiagram hM).
exact (@DPDiazParkCoefficients.prime_local_sharpness S F p hp pS sat
  (DPMackeyFusion.full_mackey_of_inclusions hM)).
Qed.

(** Arbitrary commutative Z_(p)-algebras, including the zero ring, are
    handled by restriction of scalars, not by a finite-dimensional model. *)
Theorem algebra_sharpness_from_prime_local (R : comPzRingType)
    (phi : {rmorphism DPPrimeLocal.type p -> R})
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) n :
    forall q : derived_limit R (mackey_codiagram (centric_inclusion F) M) n.+1, q = 0.
Proof.
apply/(@DPMackeyScalarRestriction.restricted_mackey_higher_limit_zero_iff
  Zp R phi (orbit_category F) (DPFusionMackey.fusion_mackey_shape F) M
  (centric_orbit_category F) (centric_inclusion F) n.+1).
exact (@DPDiazParkCoefficients.prime_local_sharpness S F p hp pS sat
  (@DPMackeyScalarRestriction.restricted_mackey Zp R phi (orbit_category F)
    (DPFusionMackey.fusion_mackey_shape F) M) n).
Qed.

Theorem field_corollary_from_prime_local (K : fieldType) (charp : p \in [pchar K])
    (M : mackey_module K (DPFusionMackey.fusion_mackey_shape F)) n :
    forall q : derived_limit K (mackey_codiagram (centric_inclusion F) M) n.+1, q = 0.
Proof.
exact (@algebra_sharpness_from_prime_local [the comPzRingType of (K : Type)]
  (DPPrimeLocalUniversal.canonical_map (@DPFusionCentricAcyclicity.field_local p K charp)) M n).
Qed.

Theorem field_corollary (K : fieldType) (charp : p \in [pchar K])
    (M : mackey_pair K (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M) :
    forall n (q : derived_limit K
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
rewrite -(DPMackeyFixedDegree.inclusion_centric_codiagram hM).
exact (@field_corollary_from_prime_local K charp (DPMackeyFusion.full_mackey_of_inclusions hM)).
Qed.

Theorem diaz_park_conjecture
    (M : mackey_pair [the comPzRingType of 'F_p] (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M)
    (finite_values : finite_dimensional_values M) :
    forall n (q : derived_limit [the pzRingType of 'F_p]
      (pair_codiagram (pair_restrict M (centric_inclusion F))) n.+1), q = 0.
Proof.
exact (@field_corollary [the fieldType of 'F_p] (pchar_Fp hp) M hM).
Qed.

Theorem prime_local_main_positive
    (M : mackey_pair Zp (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M)
    (i : nat) (hi : (0 < i)%N) :
    forall q : derived_limit Zp
      (pair_codiagram (pair_restrict M (centric_inclusion F))) i, q = 0.
Proof. case: i hi => [|n] // _; exact (@prime_local_main M hM n). Qed.

Theorem field_corollary_positive (K : fieldType) (charp : p \in [pchar K])
    (M : mackey_pair K (orbit_category F)) (hM : DPMackeyFusion.inclusion_mackey_formula M)
    (i : nat) (hi : (0 < i)%N) :
    forall q : derived_limit K
      (pair_codiagram (pair_restrict M (centric_inclusion F))) i, q = 0.
Proof. case: i hi => [|n] // _; exact (@field_corollary K charp M hM n). Qed.

Theorem diaz_park_conjecture_positive
    (M : mackey_pair [the comPzRingType of 'F_p] (orbit_category F))
    (hM : DPMackeyFusion.inclusion_mackey_formula M)
    (finite_values : finite_dimensional_values M) (i : nat) (hi : (0 < i)%N) :
    forall q : derived_limit [the pzRingType of 'F_p]
      (pair_codiagram (pair_restrict M (centric_inclusion F))) i, q = 0.
Proof. case: i hi => [|n] // _; exact (@diaz_park_conjecture M hM finite_values n). Qed.
End MainTheorems.

Section CentralCollection.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable Z : {group S}.
Hypothesis cZ : DPFusionQuotient.central F Z.
Let pZ : p.-group Z := pgroupS (subsetT Z) pS.

(** Lemma 3.1(iii), retaining literal inverse functor equalities. *)
Definition quotient_collection_category_isomorphism :
    category_isomorphism (DPFusionQuotientCollection.collection_category cZ)
      (centric_orbit_category (DPFusionQuotientConstruction.system cZ)) :=
  @DPFusionQuotientCollection.collection_category_isomorphism S F Z cZ p pZ sat.

Lemma quotient_collection_object (P : DPFusionQuotientCollection.collection_object cZ) :
    val (fobj (category_iso_forward quotient_collection_category_isomorphism) P) = (val P / Z)%G.
Proof. reflexivity. Qed.

Lemma quotient_collection_map (P Q : DPFusionQuotientCollection.collection_object cZ)
    (f : orbit_hom F (val P) (val Q)) :
    fmap (category_iso_forward quotient_collection_category_isomorphism) f =
    DPFusionQuotientOrbitMaps.orbit_map cZ
      (@hom_transport (orbit_category F) (val P) (val Q)
        (DPFusionQuotientConstruction.preimage (val P / Z)%G)
        (DPFusionQuotientConstruction.preimage (val Q / Z)%G)
        (esym (DPFusionQuotientNormalization.preimage_of_quotient cZ
          (DPFusionQuotientCollection.collection_contains P)))
        (esym (DPFusionQuotientNormalization.preimage_of_quotient cZ
          (DPFusionQuotientCollection.collection_contains Q))) f).
Proof. reflexivity. Qed.

(** Lemma 3.1(iv), stronger over every pzRingType.  D is any actual
    contravariant module diagram and n is any natural number, including 0. *)
Definition quotient_collection_higher_limit_iso (R : pzRingType)
    (D : module_codiagram R (centric_orbit_category F)) n :
    @isomorphism (module_category R) (derived_limit R D n)
      (derived_limit R (DPFusionCollectionAdapter.literal_restriction cZ D) n) :=
  @DPFusionCollectionDegreewise.literal_collection_derived_iso S F Z cZ p pS pZ sat R D n.
End CentralCollection.

Section MinimalSubsystem.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable C : {group S}.
Local Notation T := [subg C]%type.
Variable H : DPFusionSystem.system [the finGroupType of T].
Hypothesis hH : forall (P Q : {group T}) (f : DPFusion.map P Q),
  DPFusionSystem.allowed H f -> DPFusionSystem.allowed F (DPFusionSubgroup.lift f).
Hypothesis hcentric : forall P : {group T},
  DPFusionSystem.centric H P -> DPFusionSystem.centric F (DPFusionSubgroup.ambient P).
Variable R : comPzRingType.
Variable M : mackey_pair R (orbit_category F).
Hypothesis hM : DPMackeyFusion.inclusion_mackey_formula M.
Let full := DPMackeyFusion.full_mackey_of_inclusions hM.
Hypothesis simpleM : mackey_simple full.
Variable Q : {group S}.
Hypothesis minimalQ : DPMackeyMinimal.subgroup_minimal full Q.
Hypothesis noncentricQ : ~~ DPFusionSystem.centric F Q.
Variable p : nat.
Hypothesis charp : p%:R = (0 : R).
Hypothesis pT : p.-group [set: T].
Hypothesis satH : DPFusionSaturation.saturated H p.

(** Lemma 4.2 on the actual restriction of the original coefficient pair. *)
Theorem minimal_subsystem_centric_limit_zero
    (y : module_limit_type (DPFusionStableLimit.centric_coefficient
      (DPFusionSubsystemRestriction.restricted_pair hH M))) : y = 0.
Proof.
exact (@DPFusionStableZero.subsystem_centric_limit_zero S F C H hH hcentric R M hM
  simpleM Q (@DPMackeyMinimalManuscript.minimal_is_least S F R full simpleM Q minimalQ)
  noncentricQ p charp pT satH y).
Qed.
End MinimalSubsystem.
End DPDiazParkManuscript.

Check DPDiazParkManuscript.prime_local_main_positive.
Check DPDiazParkManuscript.field_corollary_positive.
Check DPDiazParkManuscript.diaz_park_conjecture_positive.
Check DPDiazParkManuscript.quotient_collection_category_isomorphism.
Check DPDiazParkManuscript.quotient_collection_higher_limit_iso.
Check DPDiazParkManuscript.minimal_subsystem_centric_limit_zero.
Print Assumptions DPDiazParkManuscript.prime_local_main_positive.
Print Assumptions DPDiazParkManuscript.field_corollary_positive.
Print Assumptions DPDiazParkManuscript.diaz_park_conjecture_positive.
Print Assumptions DPDiazParkManuscript.quotient_collection_category_isomorphism.
Print Assumptions DPDiazParkManuscript.quotient_collection_higher_limit_iso.
Print Assumptions DPDiazParkManuscript.minimal_subsystem_centric_limit_zero.
