From mathcomp Require Import all_boot all_algebra rat.
From DiazPark Require Import ModuleInfrastructure ModuleIntegerIdeals PrimeLocalRing PrimeLocalIntegers.
Import GRing.Theory DPPrimeLocal DPPrimeLocalIntegers.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module DPPrimeLocalIdeals.
Section Ideals.
Variable p : nat.
Local Notation R := (DPPrimeLocal.type p).
Variable I : module_subspace [the lmodType R of R^o].

Definition integer_preimage : module_subspace [the lmodType int of int^o].
Proof.
refine (@ModuleSubspace [the pzRingType of (int : Type)] [the lmodType int of int^o] (fun n : int => I (n%:~R : R)) _ _ _).
- rewrite rmorph0; exact: subspace_zero.
- move=> x y hx hy; rewrite rmorphD; exact: subspace_add hx hy.
- move=> a x hx; change (I ((a*x)%:~R : R)); rewrite rmorphM.
  exact: (@subspace_scale R _ I (a%:~R) _ hx).
Defined.

Lemma numerator_mem (x : R) : I x -> I ((numq (value x))%:~R : R).
Proof.
move=> hx.
have h := @subspace_scale R _ I ((denq (value x))%:~R) x hx.
change (I ((denq (value x))%:~R * x)) in h.
rewrite {2}(fraction_representation x) mulrCA mulrV ?denominator_unit ?mulr1 in h.
exact h.
by [].
Qed.

Theorem ideal_principal : exists a : R, I a /\ forall x, I x -> exists c : R, c*a=x.
Proof.
have [d [hd he]] := integer_ideal_principal integer_preimage.
exists (d%:R); split; first exact hd.
move=> x hx.
have hn : integer_preimage (numq (value x)) := numerator_mem hx.
have [q hq] := (proj1 (he _)) hn.
exists ((q%:~R : R) / (denq (value x))%:~R).
rewrite {2}(fraction_representation x) hq rmorphM.
by rewrite mulrAC.
Qed.

Theorem ideal_principal_iff : exists a : R, I a /\ forall x, I x <-> exists c : R, c*a=x.
Proof.
have [a [ha he]] := ideal_principal.
exists a; split=> // x; split; first exact: he.
move=> [c <-]; exact: (@subspace_scale R _ I c _ ha).
Qed.
End Ideals.
End DPPrimeLocalIdeals.

Print Assumptions DPPrimeLocalIdeals.ideal_principal.






