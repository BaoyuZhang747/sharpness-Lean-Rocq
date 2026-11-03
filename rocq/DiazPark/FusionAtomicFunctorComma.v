From mathcomp Require Import all_ssreflect all_fingroup pgroup sylow generic_quotient.
From DiazPark Require Import Category CategoryComma CategoryInitialFamily
  GroupOrbitCategory GroupActionOrbitRepresentatives GroupActionTerminalCosets
  FusionMaps FusionSystems FusionSaturation FusionOrbit FusionAtomicFunctorPreimages
  FusionAtomicFunctorFixed FusionAtomicFunctor FusionAtomicFunctorStabilizer.
Import DPFusionOrbit DPFusionAtomicPreimages DPFusionAtomicFixed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionAtomicComma.
Section Comma.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable Q : {group S}.
Hypothesis centricQ : DPFusionSystem.centric F Q.
Hypothesis normalizedQ : DPFusionSystem.fully_normalized F Q.
Variable P : centric_object F.
Local Notation G := (outer_type F Q).
Local Notation T := (ambient_outer F Q).
Local Notation B := (DPFusionAtomicFunctor.domain F p Q).
Local Notation CC := (centric_orbit_category F).
Local Notation a := (DPFusionAtomicFunctor.comparison_functor pS sat centricQ).
Local Notation Comma := (structured_category (functor_op a) P).
Local Notation X := [the finType of orbit_hom F Q (val P)].
Local Notation act := (@DPFusionAtomicNativeStabilizer.action S F Q (val P)).
Local Notation act1 := (@DPFusionAtomicNativeStabilizer.action_one S F Q (val P)).
Local Notation actM := (@DPFusionAtomicNativeStabilizer.action_mul S F Q (val P)).
Local Notation Stab x := (@DPLeftAction.stabilizer G X act act1 actM x).

Lemma stabilizers_pgroup x : p.-group (Stab x).
Proof.
rewrite DPFusionAtomicNativeStabilizer.generic_stabilizer.
exact: DPFusionAtomicNativeStabilizer.stabilizer_pgroup (pgroupS (subsetT (val P)) pS).
Qed.
Definition sylow : p.-Sylow([set: G]) T := ambient_outer_sylow_subtype sat normalizedQ.
Definition index := @DPLeftAction.orbit_index G X act act1 actM.
Definition representative : index -> X := DPLeftAction.representative sylow stabilizers_pgroup.

Definition representative_group (i : index) : B.
Proof.
exists (Stab (representative i)); apply/andP; split.
- exact: stabilizers_pgroup.
- exact: DPLeftAction.representative_stabilizer_sub.
Defined.
Lemma representative_fixed (i : index) : fixed (val (representative_group i)) (representative i).
Proof. move=> h hh; exact: (elimT (DPLeftAction.stabilizerP act1 actM _ _) hh). Qed.

Definition representative_extension (i : index) :
  orbit_hom F (@preimage S F Q (val (representative_group i))) (val P) :=
  DPFusionAtomicFunctor.lift sat centricQ (@representative_fixed i).
Lemma representative_extension_spec i : restriction centricQ (representative_extension i) = representative i.
Proof. exact: DPFusionAtomicFunctor.lift_spec. Qed.

Definition family_object (i : index) : Comma :=
  @Build_costructured_object (opposite (opposite B)) (opposite (opposite CC))
    (functor_op (functor_op a)) P (representative_group i) (representative_extension i).

Definition restricted (x : Comma) : X := restriction centricQ (costructured_arrow x).
Lemma restricted_fixed (x : Comma) :
  DPActionTerminal.fixed act (val (costructured_source x)) (restricted x).
Proof.
exact: (@DPFusionAtomicFixed.restriction_fixed S F Q centricQ (val (costructured_source x))
  (DPFusionAtomicFunctor.object_bound (costructured_source x)) (val P) (costructured_arrow x)).
Qed.

Lemma map_restriction (H K : B) (f : hom B H K) :
  restriction centricQ (fmap a f) =
    orbit_compose (@outer_orbit S F Q (val (repr f))) (inclusion_orbit centricQ (val K)).
Proof. exact: DPFusionAtomicFunctor.raw_map_spec. Qed.

Lemma factor_restriction (x : Comma) (i : index)
    (f : hom B (costructured_source x) (representative_group i)) :
  restriction centricQ (orbit_compose (fmap a f) (representative_extension i)) =
    DPActionTerminal.coset_action act f (representative i).
Proof.
rewrite restriction_postcompose map_restriction.
rewrite (@DPFusionAtomicFunctor.orbit_assoc S F Q Q _ _).
change (orbit_compose (@outer_orbit S F Q (val (repr f)))
  (restriction centricQ (representative_extension i)) = DPActionTerminal.coset_action act f (representative i)).
by rewrite representative_extension_spec.
Qed.

Definition coset_witness (x : Comma) :=
  {i : index & {f : hom B (costructured_source x) (representative_group i) |
    DPActionTerminal.coset_action act f (representative i) == restricted x}}.

Definition selected_coset (x : Comma) : coset_witness x :=
  DPActionTerminal.terminal_coset sylow stabilizers_pgroup (@restricted_fixed x).

Definition decode (x : Comma) (t : coset_witness x) :
  {i : index & hom Comma (family_object i) x}.
Proof.
case: t=> i [f hf].
refine (existT _ i (@Build_costructured_hom (opposite (opposite B)) (opposite (opposite CC))
  (functor_op (functor_op a)) P x (family_object i) f _)).
apply: (@restriction_injective S F p pS sat Q centricQ (val (costructured_source x)) (val P)).
exact (eq_trans (@factor_restriction x i f) (eqP hf)).
Defined.

Definition encode (x : Comma) (t : {i : index & hom Comma (family_object i) x}) : coset_witness x.
Proof.
case: t=> i f.
refine (existT _ i _); exists (costructured_map f).
apply/eqP.
rewrite -(@factor_restriction x i (costructured_map f)).
exact (congr1 (@restriction S F Q centricQ (val (costructured_source x)) (val P)) (costructured_commutes f)).
Defined.

Lemma decode_encode (x : Comma) (t : {i : index & hom Comma (family_object i) x}) :
  decode (encode t) = t.
Proof.
case: t=> i f; congr (existT _ i _).
apply: costructured_hom_ext; by [].
Qed.

Definition comma_initial_family : initial_family Comma.
Proof.
refine (@Build_initial_family Comma index family_object (fun x => decode (selected_coset x)) _).
move=> x z.
rewrite -(decode_encode z).
congr (decode _).
exact: DPActionTerminal.terminal_coset_unique.
Defined.

End Comma.
End DPFusionAtomicComma.





