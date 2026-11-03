From mathcomp Require Import all_boot all_algebra all_fingroup generic_quotient boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryNaturalIso CategoryComma
  CategoryModules CategoryModuleExactness CategoryModuleRightKan CategoryFinite CategoryFiniteProducts
  CategoryFinitePullbacks CategorySliceProductFamily CategoryDerivedLimits CategoryDerivedRan
  CategoryDerivedTerminal FusionSystems FusionFiniteCategory MackeyPair MackeyPairDiagrams
  MackeyRanTransfer BurnsideRanRetraction PrimeLocalRing.
Import GRing.Theory DPPrimeLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Theorem slice_ran_positive_derived_zero (R : pzRingType) (C : category) (Top : C)
    (products : forall Q : C, @finite_product_decomposition C Top Q)
    (N : module_codiagram R (over_category C Top)) n :
    forall q : derived_limit R (fobj (module_ran R (functor_op (@over_forget C Top))) N) n.+1,
      q = 0.
Proof.
move=> q.
pose e := nat_iso_component (derived_ran_nat_iso R (functor_op (@over_forget C Top))
  (fun Q => product_comma_initial_family (products Q)) n.+1) N.
apply: (@module_iso_hom_injective R _ _ e).
rewrite module_hom_zero.
exact: slice_derived_limits_positive_zero.
Qed.

Theorem derived_retract_zero (R : pzRingType) (C : category)
    (D K : module_diagram R C) (u : nat_trans D K) (r : nat_trans K D)
    (hu : nat_comp u r = nat_id D) n
    (hK : forall q : derived_limit R K n, q = 0) :
    forall q : derived_limit R D n, q = 0.
Proof.
move=> q.
have h := @derived_limit_map_composition R C D K D u r n.
rewrite hu derived_limit_map_identity in h.
have he := congr1 (fun a : module_hom (derived_limit R D n) (derived_limit R D n) => a q) h.
change (q = module_hom_fun (derived_limit_map R r n)
  (module_hom_fun (derived_limit_map R u n) q)) in he.
transitivity (module_hom_fun (derived_limit_map R r n)
  (module_hom_fun (derived_limit_map R u n) q)); first exact he.
rewrite (hK (module_hom_fun (derived_limit_map R u n) q)).
exact: module_hom_zero.
Qed.

Section CentricAcyclicity.
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

Theorem centric_mackey_positive_derived_zero n :
    forall q : derived_limit R (pair_codiagram M) n.+1, q = 0.
Proof.
apply: (@derived_retract_zero R (opposite (fc_category C)) (pair_codiagram M)
  (@mackey_slice_ran R (fc_category C) M Top)
  (@mackey_ran_unit R (fc_category C) M Top)
  (@burnside_ran_retraction S F Top products pullbacks p hp hom_prime R phi M mackey)
  (@burnside_ran_retract S F Top products pullbacks p hp hom_prime R phi M mackey) n.+1).
exact: (@slice_ran_positive_derived_zero R (fc_category C) Top products
  (functor_comp (functor_op (@over_forget (fc_category C) Top)) (pair_codiagram M)) n).
Qed.
End CentricAcyclicity.

Print Assumptions slice_ran_positive_derived_zero.
Print Assumptions centric_mackey_positive_derived_zero.

