From mathcomp Require Import all_boot all_algebra all_fingroup boolp rat.
From DiazPark Require Import Category CategoryFinite CategoryModules
  ModuleInfrastructure MackeyModuleCarriers MackeyModuleQuotient MackeyModuleMaps
  MackeyStructures MackeySubquotients MackeyFiniteLength MackeyBarReduction
  MackeyArbitraryCoefficients ModuleCohomologyFinite PrimeLocalRing PrimeLocalFinite
  FusionSystems FusionOrbit FusionMackeyShape
  HomologicalComplex HomologicalCohomology BarComplex BarNaturality BarScalarDivisibility.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal DPPrimeLocalFinite DPFusionOrbit
  DPMackeyArbitrary DiazParkHomological DiazParkCohomology
  DiazParkBarComplex DiazParkBarNaturality.
Local Open Scope ring_scope.

Module DPMackeyPrimeLocal.

Section ScalarAnnihilation.
Variable R : comPzRingType.
Variable C : category.
Variable B : mackey_shape C.
Variable M : mackey_module R B.
Variable r : R.

Lemma mackey_scalar_kernel_killed P
    (x : mackey_value (subfunctor_mackey (mackey_scalar_kernel M r)) P) :
    r *: x = 0.
Proof.
apply: submodule_val_injective.
change (submodule_inclusion (@scalar_kernel R (mackey_value M P) r) (r *: x) =
  submodule_inclusion (@scalar_kernel R (mackey_value M P) r) 0).
rewrite linearZ linear0; exact (submodule_val_mem x).
Qed.

Lemma mackey_scalar_quotient_killed P
    (x : mackey_value (quotient_mackey (mackey_scalar_image M r)) P) :
    r *: x = 0.
Proof.
have [v <-] := quotient_pi_surjective x.
rewrite -linearZ; apply/quotient_pi_kernel.
by exists v.
Qed.

End ScalarAnnihilation.

Section FiniteLocalReduction.
Variable p : nat.
Hypothesis hp : prime p.
Local Notation R := (DPPrimeLocal.type p).
Variable C : category.
Variable D : finite_category.
Variable B : mackey_shape C.
Variable L : functor (fc_category D) C.
Hypothesis torsion_acyclic : forall M : mackey_module R B,
  (forall P (x : mackey_value M P), p%:R *: x = 0) -> mackey_bar_acyclic L M.

Theorem finite_prime_local_acyclic (M : mackey_module R B) :
    (forall P, module_finitely_generated (mackey_value M P)) -> mackey_bar_acyclic L M.
Proof.
move=> hM.
have hK := torsion_acyclic (fun P x => @mackey_scalar_kernel_killed R C B M p%:R P x).
have hQ := torsion_acyclic (fun P x => @mackey_scalar_quotient_killed R C B M p%:R P x).
apply/(positive_acyclic_cohomology (bar_complex (mackey_codiagram L M)))=> n.
apply: (@prime_local_nakayama p hp
  [the lmodType R of cohomology (bar_complex (mackey_codiagram L M)) n.+1]).
- apply: (@finite_bar_cohomology_finitely_generated R (@prime_local_noetherian p)
    D (mackey_codiagram L M) n.+1).
  move=> x; exact: hM.
- exact: (@mackey_scalar_cohomology_surjective R C (fc_category D) B L M p%:R hK hQ n).
Qed.

End FiniteLocalReduction.

Section ArbitraryLocalReduction.
Variable S : finGroupType.
Variable F : DPFusionSystem.system S.
Variable p : nat.
Hypothesis hp : prime p.
Local Notation R := (DPPrimeLocal.type p).
Variable D : finite_category.
Variable L : functor (fc_category D) (orbit_category F).
Hypothesis torsion_acyclic : forall M : mackey_module R (DPFusionMackey.fusion_mackey_shape F),
  (forall P (x : mackey_value M P), p%:R *: x = 0) -> mackey_bar_acyclic L M.

Theorem arbitrary_prime_local_acyclic
    (M : mackey_module R (DPFusionMackey.fusion_mackey_shape F)) :
    mackey_bar_acyclic L M.
Proof.
move=> n z hz.
pose N := cocycle_subfunctor (L := L) z.
have hN : forall P, module_finitely_generated (mackey_value (subfunctor_mackey N) P).
  exact: cocycle_subfunctor_finite_values.
have hc : mackey_bar_acyclic L (subfunctor_mackey N).
  exact: (@finite_prime_local_acyclic p hp (orbit_category F) D
    (DPFusionMackey.fusion_mackey_shape F) L torsion_acyclic (subfunctor_mackey N) hN).
have hl := cocycle_lift_closed hz.
have [y hy] := hc n (cocycle_lift (L := L) z) hl.
exists (bar_map_at (cocycle_inclusion (L := L) z) y).
change (bar_d (mackey_codiagram L M) n
  (bar_map_at (cocycle_inclusion (L := L) z) y) = z).
by rewrite bar_map_d hy cocycle_lift_inclusion.
Qed.

End ArbitraryLocalReduction.
End DPMackeyPrimeLocal.



