(** Actual normalizer Bousfield--Kan spectral sequence in the unnormalized
    singular-cochain replacement convention. Native page index r denotes
    E_(r+1); its second coordinate is the integer column and its third is
    total degree. No realization-unit or augmentation hypothesis remains. *)
From Coq Require Import ZArith.
From mathcomp Require Import all_ssreflect all_algebra all_fingroup pgroup zmodp all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits
  CategoryModuleLimits ModuleInfrastructure HomologicalComplex HomologicalModuleIso
  FusionSystems FusionSaturation PrimeLocalRing PrimeLocalUniversal PrimeLocalModules.
From DiazParkV16b Require Import LinkingSystem NormalizerChainIndexCategory NormalizerLinkingChainProjection CategoryNerve
  TopologicalCategory GeometricRealizationCarrier SingularCohomology SingularCochainDiagrams
  CategoryCochainReplacement FirstQuadrantFilteredPages FilteredCochainPages
  SingularCochainReplacementEdge SingularCochainFilteredSecond SingularCochainFilteredCollapse
  SingularReplacementGeometricConvergence NormalizerLinkingRealizationSharpness
  NormalizerLinkingGeometricSharpness CategoryRealizationEvaluationDecomposition
  NormalizerOrdinaryCoefficient.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPTopological DPGeometricRealization DPCategoryNerve
  DPSingularCohomology DPSingularCochainDiagrams DPSingularReplacementEdge DiazParkHomological
  DiazParkHomologicalModuleIso DPFirstQuadrantFilteredPages DPFilteredPages
  DPSingularReplacementGeometricConvergence DPNormalizerLinkingRealizationSharpness
  DPNormalizerLinkingGeometricSharpness DPCategoryRealizationEvaluationDecomposition.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPNormalizerLinkingGeometricSpectralSequence.
Section Normalizer.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Local Notation X := (normalizer_space_diagram Real L).

Section Pages.
Variable R : pzRingType.
Variable A : lmodType R.
Let K := cochain_replacement_bicomplex (singular_cochain_diagram Real A X).

Definition normalizer_page r column total_degree :=
  singular_filtered_page Real A X r column total_degree.
Definition normalizer_d r column total_degree := total_filtered_d K r column total_degree.
Definition normalizer_next_page_homology_iso r column total_degree :=
  total_filtered_next_homology_iso K r column total_degree.
Theorem normalizer_d_squared r column total_degree
    (x : normalizer_page r column total_degree) :
  normalizer_d r (Z.add column (Z.of_nat r.+1)) total_degree.+1
    (normalizer_d r column total_degree x) = 0.
Proof. exact: page_d_squared. Qed.

Definition normalizer_E2_derived_limit_iso i j : @isomorphism (module_category R)
    (normalizer_page 1 (Z.of_nat i) (i+j)%coq_nat)
    (derived_limit R (singular_cohomology_diagram Real A X j) i) :=
  singular_filtered_second_derived_limit_iso Real A X i j.
End Pages.

Section Convergence.
Variable R : comPzRingType.
Variable A : lmodType R.
Local Notation Y := (realization_space Real (nerve (DPCentricLinking.linking_category L))).
Local Notation a := (normalizer_geometric_cocone Real L).
Local Notation ha := (normalizer_geometric_augmentation_quasi_isomorphism Real L R).

Definition normalizer_E2_ordinary_group_iso i j : @isomorphism (module_category R)
    (normalizer_page A 1 (Z.of_nat i) (i+j)%coq_nat)
    (derived_limit R (@DPNormalizerOrdinaryCoefficient.coefficient S F L R A j) i) :=
  module_iso_comp (normalizer_E2_derived_limit_iso A i j)
    (@normalizer_native_higher_limit_iso Real R A S F L j i).

Definition normalizer_filtration column total_degree :=
  @singular_geometric_filtration Real R A _ X Y a ha column total_degree.
Definition normalizer_associated_graded column total_degree :=
  @singular_geometric_associated_graded Real R A _ X Y a ha column total_degree.
Definition normalizer_finite_convergence_iso i n : @isomorphism (module_category R)
    (normalizer_page A (n+i+1)%coq_nat (Z.of_nat i) n)
    (normalizer_associated_graded (Z.of_nat i) n) :=
  normalizer_geometric_finite_convergence_iso Real L A i n.
Theorem normalizer_filtration_decreasing c d n (h : Z.le c d) :
    subspace_le (normalizer_filtration d n) (normalizer_filtration c n).
Proof. exact: singular_geometric_filtration_decreasing. Qed.
Theorem normalizer_filtration_zero_full n z : normalizer_filtration Z0 n z.
Proof. exact: singular_geometric_filtration_zero_full. Qed.
Theorem normalizer_filtration_bounded i n (h : (n<i)%coq_nat) z :
    normalizer_filtration (Z.of_nat i) n z -> z=0.
Proof. exact: singular_geometric_filtration_bounded. Qed.
End Convergence.

Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.

Section Field.
Variable K : fieldType.
Variable charp : p \in [pchar K].
Variable A : lmodType K.
Local Notation hX := (@field_positive_limits Real S F L p hS sat K charp A).

Theorem field_later_positive_zero r i n
    (x : normalizer_page A r.+1 (Z.of_nat i.+1) n) : x=0.
Proof. exact (@singular_filtered_later_positive_zero Real K A _ X hX r i n x). Qed.
Theorem field_later_d_zero r i n
    (x : normalizer_page A r.+1 (Z.of_nat i) n) :
    normalizer_d A r.+1 (Z.of_nat i) n x=0.
Proof. exact (@singular_filtered_later_d_zero Real K A _ X hX r i n x). Qed.
Definition field_zero_column_back_iso r n := singular_filtered_zero_column_back_iso hX r n.
Theorem field_collapses_onto_vertical_axis :
    (forall r i n (x : normalizer_page A r.+1 (Z.of_nat i.+1) n), x=0) /\
    (forall r i n (x : normalizer_page A r.+1 (Z.of_nat i) n),
      normalizer_d A r.+1 (Z.of_nat i) n x=0).
Proof. split; [exact: field_later_positive_zero|exact: field_later_d_zero]. Qed.
End Field.

Variable hp : prime p.
Section LocalRing.
Variable R : comPzRingType.
Variable localR : DPPrimeLocalUniversal.primes_inverted p R.
Variable A : lmodType R.
Local Notation hX := (@primes_inverted_positive_limits Real S F L p hp hS sat R localR A).

Theorem primes_inverted_later_positive_zero r i n
    (x : normalizer_page A r.+1 (Z.of_nat i.+1) n) : x=0.
Proof. exact (@singular_filtered_later_positive_zero Real R A _ X hX r i n x). Qed.
Theorem primes_inverted_later_d_zero r i n
    (x : normalizer_page A r.+1 (Z.of_nat i) n) :
    normalizer_d A r.+1 (Z.of_nat i) n x=0.
Proof. exact (@singular_filtered_later_d_zero Real R A _ X hX r i n x). Qed.
Theorem primes_inverted_collapses_onto_vertical_axis :
    (forall r i n (x : normalizer_page A r.+1 (Z.of_nat i.+1) n), x=0) /\
    (forall r i n (x : normalizer_page A r.+1 (Z.of_nat i) n),
      normalizer_d A r.+1 (Z.of_nat i) n x=0).
Proof. split; [exact: primes_inverted_later_positive_zero|exact: primes_inverted_later_d_zero]. Qed.
End LocalRing.

Theorem prime_field_collapses_onto_vertical_axis (A : lmodType [the fieldType of 'F_p]) :
    (forall r i n (x : normalizer_page A r.+1 (Z.of_nat i.+1) n), x=0) /\
    (forall r i n (x : normalizer_page A r.+1 (Z.of_nat i) n),
      normalizer_d A r.+1 (Z.of_nat i) n x=0).
Proof. exact (@field_collapses_onto_vertical_axis _ (pchar_Fp hp) A). Qed.

Theorem prime_local_algebra_collapses_onto_vertical_axis (R : comPzRingType)
    (phi : {rmorphism DPPrimeLocal.type p -> R}) (A : lmodType R) :
    (forall r i n (x : normalizer_page A r.+1 (Z.of_nat i.+1) n), x=0) /\
    (forall r i n (x : normalizer_page A r.+1 (Z.of_nat i) n),
      normalizer_d A r.+1 (Z.of_nat i) n x=0).
Proof.
exact (@primes_inverted_collapses_onto_vertical_axis R
  (DPPrimeLocalModules.scalar_map_implies_primes_inverted hp phi) A).
Qed.
End Normalizer.
End DPNormalizerLinkingGeometricSpectralSequence.
