(** Invertibility of the canonical comma-coordinate map. The centraliser
    linking system is constructed from L; its stable-elements map is the
    already proved Task 1 subgroup edge. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup abelian zmodp
  boolp all_classical reals topology.
From DiazPark Require Import Category CategoryModules CategoryModuleLimits
  CategoryModuleExactness CategoryStructured HomologicalModuleIso
  FusionSystems FusionSaturation FusionOrbit FusionCentralizer
  FusionCentralizerSaturation FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem LinkingCommaCategory CategoryNerve
  CategoryConstantCohomology GroupCohomologyBase GroupCohomologyOrbitCoefficient
  GroupCohomologyPullback GroupClassifyingCohomology SingularCohomology
  GeometricRealizationMaps RealizationNerveCohomology RealizationNerveCohomologyUnconditional.
From DiazParkV28 Require Import RightKanCohomology.
From DiazParkV29 Require Import MainSubgroup.
From DiazParkBLO Require Import BLODiagram BLODiagramCentralizerBase BLODiagramCentralizerSystem
  BLODiagramCentralizerEquivalence BLOCohomologyNative BLOCohomologyMap
  BLOCohomologyComma BLOCohomologyDistinguished BLOCohomologyAdjunction
  BLOCohomologyCentralizerMaps BLOE3Pointwise BLOE3Chart.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomologicalModuleIso DPFusionOrbit
  DPFusionCentralizerCoverProjection DPBLODiagram DPBLOCentralizerSystem
  DPBLOCentralizerEquivalence DPCategoryNerve DPSingularCohomology
  DPGeometricRealizationMaps DPRealizationNerveCohomology
  DPRealizationNerveCohomologyUnconditional.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPBLOCohomologyPointwise.
Section Pointwise.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable n : nat.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation K := [the fieldType of 'F_p].
Local Notation R := [the comPzRingType of (K : Type)].
Local Notation A := [the lmodType K of K^o].
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation CL := (@centralizer_linking_system S F L p pS sat B).
Local Notation inc := (@centralizer_inclusion S F L p pS sat B).
Local Notation native := (@DPBLOCohomologyNative.native_coefficient Real S F L p R A n).
Local Notation Hn := (@DPV28RightKanCohomology.H_n S F p n).
Local Notation r := (@DPBLOCohomologyMap.native_to_ran Real S F L p R A n B).
Local Notation old := (@DPV28RightKanCohomology.pointwise_native_limit_iso S F p pS sat n B).

Definition centralizer_native_iso :=
  @DPBLOCohomologyAdjunction.native_pull_iso Real R A
    (DPCentricLinking.linking_category CL) (enlarged_category L E) inc
    (@centralizer_retraction S F L p pS sat B)
    (@centralizer_adjunction S F L p pS sat B) n.

Lemma centralizer_abelian : abelian E.
Proof. have /and3P[_ h _] := valP B; exact: abelem_abelian h. Qed.

Lemma centralizer_saturated : DPFusionSaturation.saturated CF p.
Proof.
have /and3P[_ _ h] := valP B.
exact (@DPFusionCentralizerSaturation.centralizer_saturated S F E
  centralizer_abelian p pS sat h).
Qed.

Definition centralizer_stable_iso :=
  @DPV29LinkingSubgroup.native_edge_iso Real _ CF CL p
    (@DPFusionCentralizerSaturation.centralizer_pgroup S E p pS)
    centralizer_saturated K (pchar_Fp hp) A n.

Definition centralizer_comparison := module_iso_comp centralizer_native_iso centralizer_stable_iso.

Lemma pointwise_square :
    module_hom_comp r (iso_hom old) = iso_hom centralizer_comparison.
Proof.
apply module_hom_ext=> x; apply module_limit_val_injective.
apply functional_extensionality_dep=> P.
have hc := congr1 (fun h : module_hom (fobj Hn B)
  (fobj (DPGroupCohomologyOrbitCoefficient.centric_coefficient CF A n) P) => module_hom_fun h (r x))
  (@DPBLOE3Pointwise.pointwise_native_coordinate S F p pS sat n B P).
change (module_limit_val (module_hom_fun (iso_hom old) (r x)) P =
  module_hom_fun (component (iso_inv
    (@DPV28RightKanCohomology.centralizer_coefficient_nat_iso S F p pS sat n B)) P)
    (module_limit_val (r x) (@DPBLOE3Pointwise.local_comma_point S F p pS sat B P))) in hc.
change (module_limit_val (module_hom_fun (iso_hom old) (r x)) P =
  module_limit_val (module_hom_fun (iso_hom centralizer_stable_iso)
    (module_hom_fun (iso_hom centralizer_native_iso) x)) P).
Time refine (eq_trans hc _).
Time rewrite (@DPBLOE3Chart.centralizer_coefficient_inverse_chart S F p pS sat n B P).
Time rewrite (@DPBLOCohomologyMap.native_to_ran_coordinate Real S F L p R A n B x
  (@DPBLOE3Pointwise.local_comma_point S F p pS sat B P)).
Time rewrite (@DPBLOCohomologyCentralizerMaps.comma_centralizer_distinguished S F L p pS sat B P).
Time rewrite (@DPV29LinkingSubgroup.native_edge_component Real _ CF CL p
  (@DPFusionCentralizerSaturation.centralizer_pgroup S E p pS) centralizer_saturated
  K (pchar_Fp hp) A n (module_hom_fun (iso_hom centralizer_native_iso) x) P).
Time rewrite (@DPBLOCohomologyAdjunction.native_pull_iso_forward Real R A
  (DPCentricLinking.linking_category CL) (enlarged_category L E) inc
  (@centralizer_retraction S F L p pS sat B)
  (@centralizer_adjunction S F L p pS sat B) n x).
Time have h1 := @comparison_iso_unconditional_natural Real R A
  (DPGroupCohomology.group_category [subg (val P)]%type)
  (DPCentricLinking.linking_category CL) (DPLinkingComma.distinguished_functor CL P) n
  (singular_cohomology_map Real (realization_map Real (nerve_map inc)) A n x).
Time have h2 := congr1 (fun z : DPCategoryConstantCohomology.value R A
    (DPCentricLinking.linking_category CL) n =>
  module_hom_fun (DPCategoryConstantCohomology.pull A
    (DPLinkingComma.distinguished_functor CL P) n) z)
  (@comparison_iso_unconditional_natural Real R A
    (DPCentricLinking.linking_category CL) (enlarged_category L E) inc n x).
Time have hd := congr1 (fun h : module_hom
    (DPCategoryConstantCohomology.value R A (enlarged_category L E) n)
    (DPGroupCohomology.value R [subg (val P)]%type A n) => module_hom_fun h
    (module_hom_fun (iso_hom (comparison_iso_unconditional Real A (enlarged_category L E) n)) x))
  (@DPBLOCohomologyCentralizerMaps.distinguished_pull_square S F L p pS sat B R A n P).
Time exact (esym (eq_trans h1 (eq_trans h2 hd))).
Qed.

Definition factor_iso : @isomorphism (module_category K) (fobj native B) (fobj Hn B) :=
  module_iso_comp centralizer_comparison (iso_symm old).

Lemma factor_iso_forward (x : fobj native B) :
    module_hom_fun (iso_hom factor_iso) x = r x.
Proof.
apply (@module_iso_hom_injective K _ _ old).
change (module_hom_fun (iso_hom old)
  (module_hom_fun (iso_inv old) (module_hom_fun (iso_hom centralizer_comparison) x)) =
  module_hom_fun (iso_hom old) (r x)).
rewrite module_iso_inv_hom_apply.
symmetry; exact (congr1 (fun h => module_hom_fun h x) pointwise_square).
Qed.

Definition pointwise_iso : @isomorphism (module_category K) (fobj native B) (fobj Hn B).
Proof.
refine (@Build_isomorphism (module_category K) (fobj native B) (fobj Hn B)
  r (iso_inv factor_iso) _ _).
- apply module_hom_ext=> x.
  change (module_hom_fun (iso_inv factor_iso) (r x) = x).
  rewrite -factor_iso_forward; exact: module_iso_hom_inv_apply.
- apply module_hom_ext=> x.
  change (r (module_hom_fun (iso_inv factor_iso) x) = x).
  rewrite -factor_iso_forward; exact: module_iso_inv_hom_apply.
Defined.

Lemma pointwise_iso_hom : iso_hom pointwise_iso = r.
Proof. reflexivity. Qed.
End Pointwise.
End DPBLOCohomologyPointwise.
