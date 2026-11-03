From mathcomp Require Import all_boot all_algebra rat zmodp.
From DiazPark Require Import PrimeLocalRing PrimeLocalIntegers PrimeLocalUniversal.
Import GRing.Theory DPPrimeLocal DPPrimeLocalIntegers DPPrimeLocalUniversal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPPrimeLocalResidue.
Section Residue.
Variable p : nat.
Hypothesis hp : prime p.
Local Notation Zp := (DPPrimeLocal.type p).

Lemma field_primes_inverted : primes_inverted p [the comPzRingType of 'F_p].
Proof.
move=> n hn; exists ((n%:R : 'F_p)^-1).
apply: mulVr; by rewrite unitFpE.
Qed.

Definition residue : {rmorphism Zp -> 'F_p} :=
  @canonical_map p [the comPzRingType of 'F_p] field_primes_inverted.

Lemma residue_integer (n : int) : residue (n%:~R : Zp) = n%:~R.
Proof. exact: rmorph_int. Qed.

Lemma residue_natural (n : nat) : residue (n%:R : Zp) = n%:R.
Proof. exact: rmorph_nat. Qed.

Theorem residue_surjective : forall x : 'F_p, exists y : Zp, residue y = x.
Proof.
move=> x; exists ((val x)%:R : Zp).
by rewrite residue_natural natr_Zp.
Qed.

Lemma residue_denominator (x : Zp) :
    residue x * (denq (value x))%:~R = (numq (value x))%:~R.
Proof. exact: scalar_map_denominator. Qed.

Theorem residue_kernel (x : Zp) :
    residue x = 0 <-> exists y : Zp, p%:R * y = x.
Proof.
split.
- move=> hx.
  have hn : ((numq (value x))%:~R : 'F_p) = 0.
    by rewrite -(residue_denominator x) hx mul0r.
  have hd : (p %| numq (value x))%Z.
    by rewrite (dvdz_pcharf (pchar_Fp hp)) hn eqxx.
  have [q hq] := (dvdzP hd).
  exists ((q%:~R : Zp) / (denq (value x))%:~R).
  rewrite {2}(fraction_representation x) hq rmorphM.
  by rewrite mulrA [p%:R * q%:~R]mulrC.
- move=> [y <-].
  by rewrite rmorphM residue_natural (pchar_Fp_0 hp) mul0r.
Qed.

Lemma residue_prime : residue (p%:R : Zp) = 0.
Proof. by rewrite residue_natural (pchar_Fp_0 hp). Qed.

End Residue.
End DPPrimeLocalResidue.

Print Assumptions DPPrimeLocalResidue.residue_surjective.
Print Assumptions DPPrimeLocalResidue.residue_kernel.
