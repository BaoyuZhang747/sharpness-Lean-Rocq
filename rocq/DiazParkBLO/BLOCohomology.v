(** BLO-02: native ordinary mod-p cohomology of the actual enlarged linking
    diagram is naturally isomorphic to the existing E3 right Kan extension.
    The isomorphism has the canonical comma-coordinate forward map. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup zmodp
  all_classical reals topology.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso
  CategoryModules CategoryModuleLimits CategoryStructured CategoryComma
  FusionSystems FusionSaturation FusionCentralizerCoverProjection.
From DiazParkV16b Require Import LinkingSystem.
From DiazParkV28 Require Import RightKanCohomology FusionCentralizerComma.
From DiazParkBLO Require Import BLOCohomologyNative BLOCohomologyMap BLOCohomologyPointwise.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusionCentralizerCoverProjection.
Local Open Scope group_scope.

Module DPBLOCohomology.
Section Coefficient.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p n : nat.
Local Notation K := [the fieldType of 'F_p].
Local Notation R := [the comPzRingType of (K : Type)].
Local Notation A := [the lmodType K of K^o].

Definition native_coefficient : module_diagram K (elementary_category F p) :=
  @DPBLOCohomologyNative.native_coefficient Real S F L p R A n.

Definition native_ran_trans : nat_trans native_coefficient
    (@DPV28RightKanCohomology.H_n S F p n) :=
  @DPBLOCohomologyMap.native_ran_trans Real S F L p R A n.
End Coefficient.

Section Comparison.
Variable Real : realType.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable L : DPCentricLinking.system F.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable n : nat.
Local Notation K := [the fieldType of 'F_p].
Local Notation R := [the comPzRingType of (K : Type)].
Local Notation A := [the lmodType K of K^o].
Local Notation EC := (elementary_category F p).
Local Notation native := (@native_coefficient Real S F L p n).
Local Notation Hn := (@DPV28RightKanCohomology.H_n S F p n).

Definition native_ran_nat_iso :
    @isomorphism (functor_category EC (module_category K)) native Hn.
Proof.
apply (@nat_iso_of_components EC (module_category K) native Hn
  (fun E => @DPBLOCohomologyPointwise.pointwise_iso Real S F L p hp pS sat n E)).
move=> E E' u.
exact (@DPBLOCohomologyMap.native_to_ran_naturality Real S F L p R A n E E' u).
Defined.

Lemma native_ran_nat_iso_hom : iso_hom native_ran_nat_iso =
    @native_ran_trans Real S F L p n.
Proof. apply nat_trans_ext=> E; reflexivity. Qed.

Lemma native_ran_nat_iso_component (E : EC) :
    component (iso_hom native_ran_nat_iso) E =
    @DPBLOCohomologyMap.native_to_ran Real S F L p R A n E.
Proof. reflexivity. Qed.

Theorem native_ran_all_arrow_square (E E' : EC) (u : hom EC E E') :
    module_hom_comp (fmap native u) (component (iso_hom native_ran_nat_iso) E') =
    module_hom_comp (component (iso_hom native_ran_nat_iso) E) (fmap Hn u).
Proof. exact (naturality (iso_hom native_ran_nat_iso) u). Qed.
End Comparison.
End DPBLOCohomology.
