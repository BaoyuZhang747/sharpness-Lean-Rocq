From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryComma
  CategoryModules CategoryModuleLinear CategoryModuleExactness CategoryModuleRightKan
  CategoryFinite CategoryFiniteProducts CategoryFinitePullbacks FusionSystems FusionFiniteCategory
  MackeyPair MackeyPairDiagrams MackeyRanTransfer BurnsideTopOperatorInvertible
  PrimeLocalRing HomologicalModuleIso.
Import GRing.Theory DPPrimeLocal DiazParkHomologicalModuleIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Retraction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Local Notation C := (DPFusionFinite.centric_finite_category F).
Variable Top : fc_object C.
Variable products : forall Q : fc_object C, @finite_product_decomposition (fc_category C) Top Q.
Variable pullbacks : forall (A B T : fc_object C) (f : fc_hom C A T) (g : fc_hom C B T),
  @finite_pullback_decomposition (fc_category C) A B T f g.
Variable p : nat.
Hypothesis hp : prime p.
Hypothesis hom_prime : forall X : fc_object C, coprime p #|fc_hom C X Top|.
Variable R : comPzRingType.
Variable phi : {rmorphism DPPrimeLocal.type p -> R}.
Variable M : mackey_pair R (fc_category C).
Hypothesis mackey : forall (A B T : fc_object C) (f : fc_hom C A T) (g : fc_hom C B T)
  (x : pair_value M A), pair_pull M g (pair_push M f x) =
    \sum_(i : pb_index (pullbacks f g)) pair_push M (pb_right (pullbacks f g) i)
      (pair_pull M (pb_left (pullbacks f g) i) x).

Local Notation D := (pair_codiagram M).
Local Notation K := (@mackey_slice_ran R (fc_category C) M Top).
Local Notation eta := (@mackey_ran_unit R (fc_category C) M Top).
Local Notation tr := (@mackey_ran_transfer R (fc_category C) M Top products pullbacks mackey).

Definition burnside_ran_endomorphism := nat_comp eta tr.

Lemma burnside_ran_endomorphism_bijective Q :
    bijective (module_hom_fun (component burnside_ran_endomorphism Q)).
Proof.
exact (@top_transfer_restriction_bijective S F Top Q (products Q)
  (fun A B f g => pullbacks f g) p hp hom_prime R phi M
  (fun A B f g => mackey f g)).
Qed.

Definition burnside_ran_component_iso Q :
    @isomorphism (module_category R) (pair_value M Q) (pair_value M Q).
Proof.
refine (@linear_bijection_iso R _ _ (module_hom_to_linear
  (component burnside_ran_endomorphism Q)) _ _).
- exact: bij_inj (burnside_ran_endomorphism_bijective Q).
- move=> v; have [g h1 h2] := burnside_ran_endomorphism_bijective Q.
  by exists (g v); exact: h2.
Defined.

Lemma burnside_ran_component_iso_hom Q :
    iso_hom (burnside_ran_component_iso Q) = component burnside_ran_endomorphism Q.
Proof. exact: module_hom_linear_roundtrip. Qed.

Definition burnside_ran_endomorphism_iso :
    @isomorphism (functor_category (opposite (fc_category C)) (module_category R)) D D.
Proof.
refine (@nat_iso_of_components (opposite (fc_category C)) (module_category R) D D
  burnside_ran_component_iso _).
move=> Q Q' f; rewrite !burnside_ran_component_iso_hom.
exact (@naturality (opposite (fc_category C)) (module_category R) D D
  burnside_ran_endomorphism Q Q' f).
Defined.

Lemma burnside_ran_endomorphism_iso_hom :
    iso_hom burnside_ran_endomorphism_iso = burnside_ran_endomorphism.
Proof. apply: nat_trans_ext=> Q; exact: burnside_ran_component_iso_hom. Qed.

Definition burnside_ran_retraction : nat_trans K D :=
  nat_comp tr (iso_inv burnside_ran_endomorphism_iso).

Theorem burnside_ran_retract : nat_comp eta burnside_ran_retraction = nat_id D.
Proof.
apply: nat_trans_ext=> Q; apply: module_hom_ext=> x.
have h := iso_hom_inv burnside_ran_endomorphism_iso.
change (nat_comp (iso_hom burnside_ran_endomorphism_iso)
  (iso_inv burnside_ran_endomorphism_iso) = nat_id D) in h.
rewrite burnside_ran_endomorphism_iso_hom in h.
exact (congr1 (fun a : nat_trans D D => module_hom_fun (component a Q) x) h).
Qed.
End Retraction.

Print Assumptions burnside_ran_retract.


