(** Field comparison rebuilt with new comma acyclicity; no old global sharpness. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup.
From DiazPark Require Import Category CategoryModules CategoryDerivedLimits HomologicalModuleIso
 FusionSystems FusionOrbit FusionSaturation.
From DiazParkV16b Require Import LinkingSystem LinkingChainObjects NormalizerChainIndexCategory
 GroupCohomologyOrbitCoefficient NormalizerOrdinaryCoefficient NormalizerOrdinaryRanIso
 NormalizerProjectionCommaStructured NormalizerOrbitPairProjection NormalizerOrbitForgetHigherLimits
 CategoryRanAcyclicComparison.
From DiazParkV28 Require Import NormalizerLocalRouteB.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPLinkingChains DPNormalizerChainIndex DPNormalizerOrdinaryCoefficient
 DPNormalizerProjectionCommaStructured DPNormalizerOrbitForgetHigherLimits DiazParkHomologicalModuleIso.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPV28NormalizerComparison.
Section Comparison.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Variable hS : p.-group [set: S].
Variable sat : DPFusionSaturation.saturated F p.
Variable r : index_object F -> chain F.
Hypothesis hr : forall d, chain_class (r d) = d.
Variable K : fieldType.
Variable charp : p \in [pchar K].
Variable A : lmodType K.
Variable n : nat.
Local Notation I := (opposite (index_category F)).
Local Notation M := (@representative_coefficient S F L r hr K A n).
Local Notation B := (@pair_coefficient S F K
  (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n)).
Local Notation proj := (functor_op (DPNormalizerOrbitPairProjection.projection F)).
Local Notation e := (@DPNormalizerOrdinaryRanIso.field_ran_iso S F L p hS sat r hr K charp A n).
Local Notation ac := (@DPV28NormalizerLocal.field_ran_comma_acyclic S F L p hS sat K charp A n).

Definition field_pair_higher_limit_iso j : @isomorphism (module_category K)
    (derived_limit K M j) (derived_limit K B j) :=
  module_iso_comp (functor_iso (derived_limit_functor K I j) e)
    (ran_acyclic_higher_limit_iso K proj ac j).

Definition field_higher_limit_iso j : @isomorphism (module_category K)
    (derived_limit K M j)
    (derived_limit K (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n) j) :=
  module_iso_comp (field_pair_higher_limit_iso j)
    (iso_symm (@forget_higher_limit_iso S F p hS sat K
      (DPGroupCohomologyOrbitCoefficient.centric_coefficient F A n) j)).

Theorem field_pair_higher_limit_iso_hom j : iso_hom (field_pair_higher_limit_iso j) =
  module_hom_comp (derived_limit_map K (iso_hom e) j)
    (iso_hom (ran_acyclic_higher_limit_iso K proj ac j)).
Proof. reflexivity. Qed.
End Comparison.
End DPV28NormalizerComparison.
