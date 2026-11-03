From mathcomp Require Import all_ssreflect all_fingroup center abelian pgroup generic_quotient.
From DiazPark Require Import Category CategoryFibration FusionMaps FusionSystems FusionSaturation
  FusionOrbit FusionCentralizerMaps FusionCentralizer FusionCentralizerAmbient FusionCentralizerCentric
  FusionSubsystemOrbit FusionSubsystemFaithful FusionCentralizerCover FusionCentralizerCoverProjection
  FusionCentralizerCoverFibration FusionCentralizerCoverFiberObjects FusionCentralizerCoverFiberRaw FusionCentralizerCoverFiberEqualities.
Import DPFusion DPFusionOrbit DPFusionSubgroup DPFusionSubsystem DPFusionCentralizerCover
  DPFusionCentralizerCoverProjection DPFusionCentralizerCoverFiberObjects DPFusionCentralizerCoverFiberRaw.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverFiberMaps.
Section Maps.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation T := [subg 'C(E)]%type.
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation hH := (@DPFusionCentralizerAmbient.lift_allowed S F E).
Local Notation co := (@cover_of_local S F p pS sat B).
Local Notation fo := (@fiber_of_local S F p pS sat B).
Local Notation Fib := (fiber_category (functor_op (projection F p)) B).

Lemma lifted_condition (P Q : centric_object CF) (f : DPFusionSystem.arrow CF (val P) (val Q)) :
  @raw_condition S F p (co P) (co Q) (ambient_arrow hH f).
Proof.
apply/subsetP=> z Ez; apply/morphimP; exists z.
- exact: subsetP (@ambient_contains S F p B P) z Ez.
- exact Ez.
- exact: esym (lift_fixes f Ez).
Qed.
Definition lifted_cover (P Q : centric_object CF) (f : orbit_hom CF (val P) (val Q)) :
  cover_hom (co P) (co Q) := cover_class (lifted_condition (repr f)).

Lemma lifted_delta (P Q : centric_object CF) (f : orbit_hom CF (val P) (val Q)) :
  delta (lifted_cover f) = DPFusion.identity E.
Proof.
rewrite /lifted_cover delta_class; apply/esym/raw_delta_unique.
move=> z Ez; rewrite DPFusion.identity_in //; exact (lift_fixes (repr f) Ez).
Qed.

Definition fiber_map_local (P Q : centric_object CF) (f : orbit_hom CF (val Q) (val P)) :
  @fiber_hom _ _ (functor_op (projection F p)) B (fo P) (fo Q).
Proof.
refine (@Build_fiber_hom _ _ (functor_op (projection F p)) B (fo P) (fo Q) (lifted_cover f) _).
apply: DPFusionCentralizerCoverFiberEqualities.delta_fixed_over.
move=> x Ex; rewrite lifted_delta; exact: DPFusion.identity_in Ex.
Defined.

Lemma fiber_map_local_injective (P Q : centric_object CF) :
  injective (@fiber_map_local P Q).
Proof.
move=> f g he.
apply: (@DPFusionSubsystemFaithful.orbit_map_injective S F 'C(E)%G CF hH (val Q) (val P)).
exact (congr1 (fun k : @fiber_hom _ _ (functor_op (projection F p)) B (fo P) (fo Q) => val (fiber_map k)) he).
Qed.

Lemma fiber_deltaE (P Q : centric_object CF)
    (f : @fiber_hom _ _ (functor_op (projection F p)) B (fo P) (fo Q)) :
  {in E, delta (fiber_map f) =1 id}.
Proof.
exact: DPFusionCentralizerCoverFiberEqualities.delta_fixed_of_over (fiber_over f).
Qed.

Lemma fiber_raw_fixes (P Q : centric_object CF)
    (f : @fiber_hom _ _ (functor_op (projection F p)) B (fo P) (fo Q)) :
  {in E, val (repr (val (fiber_map f))) =1 id}.
Proof.
move=> z Ez.
have he := raw_deltaE (valP (fiber_map f)) Ez.
change (val (repr (val (fiber_map f))) (delta (fiber_map f) z) = z) in he.
by rewrite (fiber_deltaE f Ez) in he.
Qed.

Definition fiber_raw_local (P Q : centric_object CF)
    (f : @fiber_hom _ _ (functor_op (projection F p)) B (fo P) (fo Q)) :
    DPFusionSystem.arrow CF (val Q) (val P) :=
  Sub (DPFusionSubgroup.lower (val (repr (val (fiber_map f)))))
    (lower_allowed_of_fixes (valP (repr (val (fiber_map f)))) (fiber_raw_fixes f)).

Definition local_map_fiber (P Q : centric_object CF)
    (f : @fiber_hom _ _ (functor_op (projection F p)) B (fo P) (fo Q)) :
    orbit_hom CF (val Q) (val P) := orbit_class (fiber_raw_local f).

Lemma fiber_map_local_surjective (P Q : centric_object CF)
    (f : @fiber_hom _ _ (functor_op (projection F p)) B (fo P) (fo Q)) :
  fiber_map_local (local_map_fiber f) = f.
Proof.
apply: fiber_hom_ext; apply: val_inj.
change (DPFusionSubsystem.orbit_map hH (orbit_class (fiber_raw_local f)) = val (fiber_map f)).
rewrite DPFusionSubsystem.orbit_map_class.
have he : ambient_arrow hH (fiber_raw_local f) = repr (val (fiber_map f)).
  apply: DPFusionSystem.arrow_ext=> x Qx.
  change (DPFusionSubgroup.lift (DPFusionSubgroup.lower (val (repr (val (fiber_map f))))) x =
    val (repr (val (fiber_map f))) x).
  by rewrite lift_lower.
rewrite he; exact: reprK.
Qed.

Lemma local_map_fiber_cancel (P Q : centric_object CF) (f : orbit_hom CF (val Q) (val P)) :
  local_map_fiber (fiber_map_local f) = f.
Proof. apply: fiber_map_local_injective; exact: fiber_map_local_surjective. Qed.
End Maps.
End DPFusionCentralizerCoverFiberMaps.








