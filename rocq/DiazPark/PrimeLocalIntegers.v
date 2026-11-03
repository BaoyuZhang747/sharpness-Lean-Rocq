From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra rat.
From DiazPark Require Import PrimeLocalRing.
Import GRing.Theory Num.Theory DPPrimeLocal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPPrimeLocalIntegers.
Section Integers.
Variable p : nat.
Local Notation R := (DPPrimeLocal.type p).

Lemma value_nat (n : nat) : DPPrimeLocal.value (n%:R : R) = n%:R.
Proof. change ((val : {rmorphism R -> rat}) n%:R = n%:R); exact: rmorph_nat. Qed.

Lemma value_int (n : int) : DPPrimeLocal.value (n%:~R : R) = n%:~R.
Proof. change ((val : {rmorphism R -> rat}) n%:~R = n%:~R); exact: rmorph_int. Qed.

Lemma integer_injective : injective (intr : int -> R).
Proof.
move=> m n he; have e := congr1 (@DPPrimeLocal.value p) he.
rewrite !value_int in e; exact: intr_inj e.
Qed.

Lemma natural_injective : injective (fun n : nat => (n%:R : R)).
Proof.
move=> m n he; have e := congr1 (@DPPrimeLocal.value p) he.
rewrite !value_nat in e; apply/eqP; rewrite -eqz_nat; apply/eqP.
exact (@intr_inj [the numDomainType of (rat : Type)] m%:Z n%:Z e).
Qed.

Lemma natural_eq0 n : (n%:R == 0 :> R) = (n == 0%N).
Proof. exact (inj_eq natural_injective n 0%N). Qed.

Lemma natural_nonzero n : n != 0%N -> (n%:R : R) != 0.
Proof. by rewrite natural_eq0. Qed.

Lemma integer_unit (n : int) : n != 0 -> coprime p `|n| -> (n%:~R : R) \is a GRing.unit.
Proof.
move=> hn hc; change (DPPrimeLocal.unit_pred (n%:~R : R)).
rewrite /DPPrimeLocal.unit_pred value_int; apply/andP; split.
- by rewrite intq_eq0.
- rewrite -div1r -[1]/(1%:~R : rat); exact: DPPrimeLocal.local_fraction hc.
Qed.

Lemma coprime_prime_nonzero (hp : prime p) n : coprime p n -> n != 0%N.
Proof.
move=> hc; apply/negP=> /eqP hn.
by move: hc; rewrite hn prime_coprime // dvdn0.
Qed.

Lemma natural_unit (hp : prime p) n : coprime p n -> (n%:R : R) \is a GRing.unit.
Proof.
move=> hc; change (((n%:Z)%:~R : R) \is a GRing.unit).
apply: integer_unit; last exact hc.
rewrite eqz_nat; exact (@coprime_prime_nonzero hp n hc).
Qed.

Lemma natural_unit_of_not_dvd (hp : prime p) n :
  ~~ (p %| n)%N -> (n%:R : R) \is a GRing.unit.
Proof. move=> hn; apply: (@natural_unit hp n); by rewrite prime_coprime. Qed.

Lemma natural_inverse_mul (hp : prime p) n (hc : coprime p n) :
  (n%:R : R)^-1 * n%:R = 1.
Proof. apply: mulVr; exact: (@natural_unit hp n hc). Qed.

Lemma value_inverse x : x \is a GRing.unit ->
  DPPrimeLocal.value (x^-1 : R) = (DPPrimeLocal.value x)^-1.
Proof. exact: DPPrimeLocal.inverse_unit. Qed.

Lemma denominator_unit (x : R) :
  ((denq (DPPrimeLocal.value x))%:~R : R) \is a GRing.unit.
Proof. apply: integer_unit; [exact: denq_neq0 | exact: valP x]. Qed.

Lemma fraction_representation (x : R) :
  x = (numq (DPPrimeLocal.value x))%:~R /
      (denq (DPPrimeLocal.value x))%:~R.
Proof.
apply: DPPrimeLocal.value_injective.
change (DPPrimeLocal.value x =
  DPPrimeLocal.value ((numq (DPPrimeLocal.value x))%:~R : R) *
  DPPrimeLocal.value (((denq (DPPrimeLocal.value x))%:~R : R)^-1)).
rewrite value_inverse ?denominator_unit // !value_int divq_num_den.
by [].
Qed.

End Integers.
End DPPrimeLocalIntegers.









