(** The actual right-Kan unit for coefficients supported on one centric
    isomorphism class is an isomorphism, in full arbitrary-module generality. *)
From mathcomp Require Import all_boot all_algebra all_fingroup pgroup boolp generic_quotient.
From DiazPark Require Import Category CategoryExtensionality CategoryAdjunction
  CategoryComma CategoryStructured CategoryInitialFamily CategoryNaturalIso
  CategoryModules CategoryModuleRightKan CategoryRanUnitIso
  FusionSystems FusionSaturation FusionOrbit FusionAtomicFunctorPreimages
  FusionAtomicFunctorFixed FusionAtomicFunctorStabilizer FusionAtomicFunctor
  FusionAtomicFunctorComma FusionAtomicUnitGeometry GroupActionOrbitRepresentatives.
Import GRing.Theory DPFusionOrbit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module DPFusionAtomicUnit.
Section Unit.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable Q : {group S}.
Hypothesis centricQ : DPFusionSystem.centric F Q.
Hypothesis normalizedQ : DPFusionSystem.fully_normalized F Q.
Local Notation OC := (orbit_category F).
Local Notation CC := (centric_orbit_category F).
Local Notation B := (DPFusionAtomicFunctor.domain F p Q).
Local Notation a := (DPFusionAtomicFunctor.comparison_functor pS sat centricQ).
Local Notation family P := (@DPFusionAtomicComma.comma_initial_family S F p pS sat Q centricQ normalizedQ P).
Local Notation index P := (@DPFusionAtomicComma.index S F Q P).
Local Notation repgroup P i := (@DPFusionAtomicComma.representative_group S F p pS sat Q normalizedQ P i).

Variable R : pzRingType.
Variable D : module_codiagram R CC.
Definition atomic : Prop := forall P : CC,
  (forall e : @isomorphism OC Q (val P), False) -> forall v : fobj D P, v = 0.
Hypothesis atomicD : atomic.
Definition restricted := functor_comp (functor_op a) D.
Definition ran_restricted := fobj (module_ran R (functor_op a)) restricted.
Definition unit_map : nat_trans D ran_restricted :=
  component (adj_unit (module_ran_adjunction R (functor_op a))) D.

Lemma representative_nontrivial (P : CC)
    (hn : forall e : @isomorphism OC Q (val P), False) (i : index P) :
    val (@DPFusionAtomicComma.representative_group S F p pS sat Q normalizedQ P i) :!=: 1%G.
Proof.
  change (@DPLeftAction.stabilizer (DPFusionAtomicPreimages.outer_type F Q)
    [the finType of orbit_hom F Q (val P)]
    (@DPFusionAtomicNativeStabilizer.action S F Q (val P))
    (@DPFusionAtomicNativeStabilizer.action_one S F Q (val P))
    (@DPFusionAtomicNativeStabilizer.action_mul S F Q (val P))
    (@DPFusionAtomicComma.representative S F p pS sat Q normalizedQ P i) :!=: 1%G).
  rewrite DPFusionAtomicNativeStabilizer.generic_stabilizer.
  exact (DPFusionAtomicNativeStabilizer.stabilizer_nontrivial
    (@DPFusionAtomicComma.representative S F p pS sat Q normalizedQ P i)
    (pgroupS (subsetT (val P)) pS) centricQ hn).
Qed.

Definition unit_component_data (P : CC) :
    {e : @isomorphism (module_category R) (fobj D P) (fobj ran_restricted P) |
      iso_hom e = component unit_map P}.
Proof.
  case: (pselect (exists e : @isomorphism OC Q (val P), True)) => [hex|hn].
  - have [e _] := cid hex.
    pose i0 : index P := DPLeftAction.orbit_class
      (@DPFusionAtomicNativeStabilizer.action_one S F Q (val P))
      (@DPFusionAtomicNativeStabilizer.action_mul S F Q (val P)) (iso_hom e).
    have only_i0 : forall i : index P, i = i0.
      move=> i. exact (DPFusionAtomicGeometry.hom_orbit_index_singleton e i i0).
    pose b := @DPFusionAtomicComma.representative_extension S F p pS sat Q centricQ normalizedQ P i0.
    pose eb := DPFusionAtomicGeometry.preimage_arrow_iso centricQ e b.
    have he : iso_hom eb = b := DPFusionAtomicGeometry.preimage_arrow_iso_hom centricQ e b.
    pose eo : @isomorphism (opposite CC) P
      (fobj a (@DPFusionAtomicComma.representative_group S F p pS sat Q normalizedQ P i0)) :=
      @Build_isomorphism (opposite CC) P
        (fobj a (@DPFusionAtomicComma.representative_group S F p pS sat Q normalizedQ P i0))
        (iso_hom eb) (iso_inv eb)
        (iso_inv_hom eb) (iso_hom_inv eb).
    exists (@ran_unit_singleton_iso R (opposite B) (opposite CC) (functor_op a)
      P (family P) D i0 only_i0 eo he). reflexivity.
  - have noiso : forall e : @isomorphism OC Q (val P), False.
      move=> e. exact (hn (ex_intro _ e I)).
    have zeroT : forall i (v : fobj D
      (fobj a (@DPFusionAtomicComma.representative_group S F p pS sat Q normalizedQ P i))), v = 0.
      move=> i v. apply atomicD.
      move=> e. exact (@DPFusionAtomicGeometry.nontrivial_preimage_not_isomorphic
        S F Q centricQ
        (val (@DPFusionAtomicComma.representative_group S F p pS sat Q normalizedQ P i))
        (DPFusionAtomicFunctor.object_bound _)
        (representative_nontrivial noiso i) e).
    exists (@ran_unit_zero_iso R (opposite B) (opposite CC) (functor_op a) P (family P) D
      (@atomicD P noiso) zeroT). reflexivity.
Defined.

Definition unit_component_iso (P : CC) := proj1_sig (unit_component_data P).

Lemma unit_component_iso_hom (P : CC) : iso_hom (unit_component_iso P) = component unit_map P.
Proof. exact (proj2_sig (unit_component_data P)). Qed.

Definition atomic_unit_iso : @isomorphism (functor_category (opposite CC) (module_category R))
    D ran_restricted.
Proof.
  apply (@nat_iso_of_components (opposite CC) (module_category R) D ran_restricted
    unit_component_iso).
  move=> P U f. rewrite !unit_component_iso_hom. exact (naturality unit_map f).
Defined.

End Unit.
End DPFusionAtomicUnit.

