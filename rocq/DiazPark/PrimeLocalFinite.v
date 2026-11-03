From mathcomp Require Import all_boot all_algebra rat.
From DiazPark Require Import ModuleInfrastructure ModuleNoetherian ModuleNoetherianFinite
  ModuleNakayama PrimeLocalRing PrimeLocalIdeals PrimeLocalUnits.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPPrimeLocal.
Local Open Scope ring_scope.

Module DPPrimeLocalFinite.

Theorem prime_local_noetherian p :
    module_noetherian [the lmodType [the pzRingType of (DPPrimeLocal.type p : Type)] of (DPPrimeLocal.type p)^o].
Proof.
apply: principal_ideals_noetherian; exact: DPPrimeLocalIdeals.ideal_principal.
Qed.

Theorem prime_local_finitely_generated_noetherian p (V : lmodType [the pzRingType of (DPPrimeLocal.type p : Type)]) :
    module_finitely_generated V -> module_noetherian V.
Proof. exact (@finitely_generated_noetherian [the pzRingType of (DPPrimeLocal.type p : Type)] (@prime_local_noetherian p) V). Qed.

Theorem prime_local_nakayama p (hp : prime p) (V : lmodType [the pzRingType of (DPPrimeLocal.type p : Type)]) :
    module_finitely_generated V ->
    (forall x : V, exists y : V, p%:R *: y = x) -> forall x : V, x = 0.
Proof.
move=> hfg hs; apply: (@finitely_generated_scalar_surjective_zero
  [the comPzRingType of (DPPrimeLocal.type p : Type)] V p%:R) hs hfg.
exact: DPPrimeLocalUnits.one_sub_prime_inverse hp.
Qed.

End DPPrimeLocalFinite.






