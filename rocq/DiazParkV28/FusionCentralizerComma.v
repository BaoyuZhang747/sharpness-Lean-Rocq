(** Concrete comma and strict-fibre dictionary for the centralizer cover.
    The elementary category remains explicitly double opposite where the
    contravariant cover projection is passed to the covariant fibre API. *)
From mathcomp Require Import all_ssreflect all_fingroup pgroup generic_quotient boolp.
From DiazPark Require Import Category CategoryComma CategoryStructured CategoryAdjunction
  CategoryFibration CategoryFiberRan CategoryIsomorphism
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionCentralizer
  FusionCentralizerCover FusionCentralizerCoverProjection FusionCentralizerCoverLifts
  FusionCentralizerCoverFibration FusionCentralizerCoverFiberIso.
From DiazParkV28 Require Import CategoryFiberCommaAdjunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import DPFusion DPFusionCentralizerCover DPFusionCentralizerCoverProjection.
Local Open Scope group_scope.

Module DPV28CentralizerComma.
Section Comma.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.

Definition tau : functor (opposite (centralized_category F p))
    (opposite (opposite (elementary_category F p))) :=
  functor_op (projection F p).

Definition comma_category (B : elementary_object F p) : category :=
  structured_category tau B.

Definition comma_projection (B : elementary_object F p) :
    functor (comma_category B) (opposite (centralized_category F p)) :=
  structured_projection tau B.

Definition comma_point (B : elementary_object F p) (a : centralized_object F p)
    (theta : DPFusionSystem.arrow F (val B) (elementary (val a))) : comma_category B :=
  structured_point tau a theta.

Lemma comma_morphism_equation (B : elementary_object F p)
    (X Y : comma_category B) (f : hom (comma_category B) X Y) :
    Category.compose (structured_arrow X) (fmap tau (structured_map f)) = structured_arrow Y.
Proof. exact (structured_commutes f). Qed.

Definition kappa_E (B : elementary_object F p) :
    functor (fiber_category tau B) (comma_category B) :=
  DPV28FiberCommaAdjunction.fiber_comma_functor tau B.

Lemma kappa_E_source (B : elementary_object F p) (x : fiber_category tau B) :
    structured_source (fobj (kappa_E B) x) = fiber_point x.
Proof. reflexivity. Qed.

Lemma kappa_E_arrow (B : elementary_object F p) (x : fiber_category tau B) :
    structured_arrow (fobj (kappa_E B) x) =
      equality_arrow (Logic.eq_sym (fiber_equality x)).
Proof. reflexivity. Qed.

Lemma kappa_E_map (B : elementary_object F p) (x y : fiber_category tau B)
    (f : hom (fiber_category tau B) x y) :
    structured_map (fmap (kappa_E B) f) = fiber_map f.
Proof. reflexivity. Qed.

Lemma kappa_E_identity_object (a : centralized_object F p) :
    fobj (kappa_E (fobj tau a))
      (@Build_fiber_object _ _ tau (fobj tau a) a (Logic.eq_refl _)) =
    structured_point tau a (Category.identity (fobj tau a)).
Proof. reflexivity. Qed.

Lemma kappa_E_projection (B : elementary_object F p) :
    functor_comp (kappa_E B) (comma_projection B) = fiber_inclusion tau B.
Proof. exact (DPV28FiberCommaAdjunction.fiber_comma_projection tau B). Qed.

Hypothesis sat : DPFusionSaturation.saturated F p.

Lemma lift_object_over (a : centralized_object F p) (B : elementary_object F p)
    (theta : DPFusionSystem.arrow F (val B) (elementary (val a))) :
    fobj tau (@DPFusionCentralizerCoverLifts.centralized_target S F p sat a B theta) = B.
Proof. apply: val_inj. reflexivity. Qed.

(** A transparent record exposes the specified source and arrow. The older
    fibration packages the same construction inside an opaque have helper. *)
Definition tau_cartesian_lift (a : centralized_object F p) (B : elementary_object F p)
    (theta : DPFusionSystem.arrow F (val B) (elementary (val a))) :
    cartesian_lift tau a B theta.
Proof.
refine (@Build_cartesian_lift (opposite (centralized_category F p))
  (opposite (opposite (elementary_category F p))) tau a B theta
  (@DPFusionCentralizerCoverLifts.centralized_target S F p sat a B theta)
  (@lift_object_over a B theta)
  (@DPFusionCentralizerCoverLifts.lift_arrow S F p sat a B theta) _ _).
- apply: DPFusionSystem.arrow_ext=> x Bx.
  change (delta (@DPFusionCentralizerCoverLifts.lift_arrow S F p sat a B theta) x =
    DPFusion.compose (val (@equality_arrow (opposite (opposite (elementary_category F p)))
      _ _ (@lift_object_over a B theta))) (val theta) x).
  rewrite DPFusionCentralizerCoverLifts.lift_delta DPFusion.compose_in //
    DPFusionCentralizerCoverFibration.elementary_equality_arrowE //.
- exact: DPFusionCentralizerCoverLifts.lift_cocartesian.
Defined.

Definition tau_fibration : fibration tau :=
  fun a B theta => @tau_cartesian_lift a B theta.

Definition nu_E (B : elementary_object F p) :
    functor (comma_category B) (fiber_category tau B) :=
  DPV28FiberCommaAdjunction.fiber_comma_right_adjoint tau_fibration B.

Definition kappa_E_adjunction (B : elementary_object F p) :
    adjunction (kappa_E B) (nu_E B) :=
  DPV28FiberCommaAdjunction.fiber_comma_adjunction tau_fibration B.

Lemma nu_E_source (B : elementary_object F p) (X : comma_category B) :
    fiber_point (fobj (nu_E B) X) =
      @DPFusionCentralizerCoverLifts.centralized_target S F p sat
        (structured_source X) B (structured_arrow X).
Proof. reflexivity. Qed.

Lemma nu_E_counit_arrow (B : elementary_object F p) (X : comma_category B) :
    structured_map (component (adj_counit (kappa_E_adjunction B)) X) =
      @DPFusionCentralizerCoverLifts.lift_arrow S F p sat
        (structured_source X) B (structured_arrow X).
Proof. reflexivity. Qed.

Hypothesis pS : p.-group [set: S].

Definition centralizer_fiber_iso (B : elementary_object F p) :
    category_isomorphism
      (opposite (DPFusionOrbit.centric_orbit_category (DPFusionCentralizer.system F (val B))))
      (fiber_category tau B) :=
  @DPFusionCentralizerCoverFiberIso.centralizer_fiber_isomorphism S F p pS sat B.

Definition centralizer_to_comma (B : elementary_object F p) :
    functor
      (opposite (DPFusionOrbit.centric_orbit_category (DPFusionCentralizer.system F (val B))))
      (comma_category B) :=
  functor_comp (category_iso_forward (centralizer_fiber_iso B)) (kappa_E B).

End Comma.
End DPV28CentralizerComma.
