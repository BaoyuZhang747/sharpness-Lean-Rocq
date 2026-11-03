From mathcomp Require Import all_boot all_algebra rat intdiv.
From DiazPark Require Import PrimeLocalRing PrimeLocalIntegers.
Import GRing.Theory DPPrimeLocal DPPrimeLocalIntegers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPPrimeLocalUnits.
Section LocalUnits.
Variable p : nat.
Hypothesis hp : prime p.
Local Notation R := (DPPrimeLocal.type p).

Lemma numerator_coprime (a : R) :
    coprime p `|numq (value a) * (p : int) + denq (value a)|.
Proof.
change (coprimez (p : int) (numq (value a) * (p : int) + denq (value a))).
rewrite /coprimez gcdzMDl.
exact: valP a.
Qed.

Lemma one_add_prime_fraction (a : R) :
    1 + p%:R * a =
      ((numq (value a) * (p : int) + denq (value a))%:~R : R) /
        (denq (value a))%:~R.
Proof.
pose n := numq (value a); pose d := denq (value a).
have hd : (d%:~R : R) \is a GRing.unit := denominator_unit a.
have ha : a = (n%:~R : R) / d%:~R := fraction_representation a.
change (1 + p%:R * a = ((n * (p : int) + d)%:~R : R) / d%:~R).
rewrite rmorphD rmorphM mulrDl (mulrV hd) addrC ha.
by rewrite mulrCA mulrA.
Qed.

Theorem one_add_prime_unit (a : R) : (1 + p%:R * a) \is a GRing.unit.
Proof.
rewrite one_add_prime_fraction unitrM unitrV denominator_unit andbT.
apply: integer_unit; last exact: numerator_coprime.
have hn := @coprime_prime_nonzero p hp _ (numerator_coprime a).
by rewrite absz_eq0 in hn.
Qed.

Theorem one_sub_prime_unit (a : R) : (1 - p%:R * a) \is a GRing.unit.
Proof. by have h := one_add_prime_unit (-a); rewrite mulrN in h. Qed.

Theorem one_sub_prime_inverse (a : R) :
    exists b : R, b * (1 - p%:R * a) = 1.
Proof. exists (1 - p%:R * a)^-1; exact: mulVr (one_sub_prime_unit a). Qed.
End LocalUnits.
End DPPrimeLocalUnits.

Print Assumptions DPPrimeLocalUnits.one_add_prime_unit.
Print Assumptions DPPrimeLocalUnits.one_sub_prime_inverse.
