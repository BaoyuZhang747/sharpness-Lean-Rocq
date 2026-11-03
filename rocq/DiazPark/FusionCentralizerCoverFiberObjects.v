From mathcomp Require Import all_ssreflect all_fingroup center abelian pgroup generic_quotient boolp.
From DiazPark Require Import Category CategoryFibration FusionMaps FusionSystems FusionSaturation
  FusionOrbit FusionCentralizerMaps FusionCentralizer FusionCentralizerCentric
  FusionCentralizerCover FusionCentralizerCoverProjection.
Import DPFusion DPFusionOrbit DPFusionSubgroup DPFusionCentralizerCover DPFusionCentralizerCoverProjection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope group_scope.
Local Open Scope quotient_scope.

Module DPFusionCentralizerCoverFiberObjects.
Section Objects.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis pS : p.-group [set: S].
Hypothesis sat : DPFusionSaturation.saturated F p.
Variable B : elementary_object F p.
Local Notation E := (val B).
Local Notation T := [subg 'C(E)]%type.
Local Notation CF := (DPFusionCentralizer.system F E).
Local Notation Fib := (fiber_category (functor_op (projection F p)) B).

Lemma elementary_abelian : abelian E.
Proof. have /and3P[_ hB _] := valP B; exact: abelem_abelian hB. Qed.
Lemma elementary_centralized : DPFusionSystem.fully_centralized F E.
Proof. by have /and3P[_ _ hB] := valP B. Qed.

Lemma ambient_centric (P : centric_object CF) : DPFusionSystem.centric F (ambient (val P)).
Proof. exact (@DPFusionCentralizerCentric.centralizer_centric_ambient_centric S F E elementary_abelian p pS sat elementary_centralized (val P) (valP P)). Qed.
Lemma ambient_contains (P : centric_object CF) : E \subset ambient (val P).
Proof. exact (@DPFusionCentralizerCentric.E_sub_of_centric S F E elementary_abelian (val P) (valP P)). Qed.
Lemma ambient_center (P : centric_object CF) : E \subset 'Z(ambient (val P)).
Proof.
apply/subsetIP; split; first exact: ambient_contains.
rewrite centsC; exact: ambient_sub.
Qed.
Definition cover_of_local (P : centric_object CF) : cover_object F p.
Proof.
exists (Sub (ambient (val P)) (ambient_centric P), E).
have /and3P[ntE abE _] := valP B; apply/and3P; split=> //.
exact: ambient_center.
Defined.
Definition centralized_of_local (P : centric_object CF) : centralized_object F p :=
  Sub (cover_of_local P) elementary_centralized.
Lemma projection_of_local (P : centric_object CF) : projection_object (centralized_of_local P) = B.
Proof. exact: val_inj. Qed.
Definition fiber_of_local (P : centric_object CF) : Fib :=
  @Build_fiber_object (opposite (centralized_category F p))
    (opposite (opposite (elementary_category F p))) (functor_op (projection F p)) B
    (centralized_of_local P) (projection_of_local P).

Definition cover_of_fiber (X : Fib) : cover_object F p := val (fiber_point X).
Lemma fiber_elementary (X : Fib) : elementary (cover_of_fiber X) = E.
Proof. exact (congr1 val (fiber_equality X)). Qed.
Lemma fiber_sub_centralizer (X : Fib) : carrier (cover_of_fiber X) \subset 'C(E).
Proof.
rewrite -(fiber_elementary X) centsC.
exact: subset_trans (elementary_center (cover_of_fiber X)) (subsetIr _ _).
Qed.
Definition local_group (X : Fib) : {group T} := (subg 'C(E) @* carrier (cover_of_fiber X))%G.
Lemma local_group_ambient (X : Fib) : ambient (local_group X) = carrier (cover_of_fiber X).
Proof. apply: val_inj; exact: subgmK (fiber_sub_centralizer X). Qed.
Lemma local_group_centric (X : Fib) : DPFusionSystem.centric CF (local_group X).
Proof.
apply: DPFusionCentralizerCentric.ambient_centric_centralizer_centric.
rewrite local_group_ambient; exact: carrier_centric.
Qed.
Definition local_of_fiber (X : Fib) : centric_object CF := Sub (local_group X) (local_group_centric X).

Lemma local_fiber_cancel (P : centric_object CF) : local_of_fiber (fiber_of_local P) = P.
Proof.
apply: val_inj; apply: ambient_injective.
exact: local_group_ambient.
Qed.
Lemma fiber_object_ext (X Y : Fib) : fiber_point X = fiber_point Y -> X = Y.
Proof.
case: X=> X hx; case: Y=> Y hy /=; move=> e; subst Y.
have -> : hx = hy := Prop_irrelevance _ _; reflexivity.
Qed.
Lemma fiber_local_cancel (X : Fib) : fiber_of_local (local_of_fiber X) = X.
Proof.
apply: fiber_object_ext; apply: val_inj; apply: val_inj.
apply: injective_projections.
- apply: val_inj; exact: local_group_ambient.
- exact: esym (fiber_elementary X).
Qed.
End Objects.
End DPFusionCentralizerCoverFiberObjects.







