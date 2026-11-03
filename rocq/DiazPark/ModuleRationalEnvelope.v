From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp rat.
From DiazPark Require Import BarFreeModule ModuleInfrastructure
  MackeyModuleCarriers MackeyModuleQuotient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory DiazParkFreeModule.
Local Open Scope ring_scope.
Local Notation "M ^z" := (zmodule M) (format "M ^z") : type_scope.

(** An arbitrary abelian group embeds into a divisible group.  The target
    is the additive quotient of a rational free module by the integral
    relations of the original group.  No injectivity theorem is assumed. *)
Module DiazParkRationalEnvelope.

Section CoefficientCast.
Variable X : Type.

Definition integer_free := free_module [the pzRingType of (int : Type)] X.
Definition rational_free := free_module [the pzRingType of (rat : Type)] X.

Definition cast_coefficients (a : integer_free) : coefficient_product [the pzRingType of (rat : Type)] X :=
  fun x => (free_coefficient a x)%:~R.

Lemma cast_finite_support a : has_finite_support (cast_coefficients a).
Proof.
exists (free_support a); move=> x hx.
by rewrite /cast_coefficients (free_coefficient_outside hx) mulr0z.
Qed.

Definition free_cast (a : integer_free) : rational_free^z :=
  @submodule_in [the pzRingType of (rat : Type)]
    (coefficient_product [the pzRingType of (rat : Type)] X)
    (finite_support_subspace [the pzRingType of (rat : Type)] X)
    (cast_coefficients a) (cast_finite_support a).

Lemma free_cast_coefficient a x :
  free_coefficient (free_cast a) x = (free_coefficient a x)%:~R.
Proof. reflexivity. Qed.

Lemma free_cast_additive : additive free_cast.
Proof.
move=> a b; apply: free_coefficient_ext=> x.
change ((free_coefficient a x - free_coefficient b x)%:~R =
  (free_coefficient a x)%:~R - (free_coefficient b x)%:~R :> rat).
exact: intrB.
Qed.

HB.instance Definition _ := GRing.isAdditive.Build integer_free rational_free^z
  free_cast free_cast_additive.

Lemma free_cast_linear : linear free_cast.
Proof.
move=> z a b; rewrite raddfD; congr (_ + _).
exact: raddf_int_scalable.
Qed.

HB.instance Definition _ := GRing.isLinear.Build int integer_free rational_free^z
  _ free_cast free_cast_linear.

Lemma free_cast_injective : injective free_cast.
Proof.
move=> a b hab; apply: free_coefficient_ext=> x.
apply: (@intr_inj [the numDomainType of (rat : Type)]).
have heq := congr1 (fun v : rational_free => free_coefficient v x) hab.
by rewrite !free_cast_coefficient in heq.
Qed.

Lemma free_cast_basis x : free_cast (free_basis [the pzRingType of (int : Type)] x) =
  free_basis [the pzRingType of (rat : Type)] x.
Proof.
apply: free_coefficient_ext=> y.
rewrite free_cast_coefficient !free_basis_coefficient.
by case: (x == y); rewrite ?mulr0z ?mulr1z.
Qed.

End CoefficientCast.

Section Envelope.
Variable A : zmodType.

Definition presentation : {linear integer_free A -> A^z} :=
  (free_lift (fun x : A => (x : A^z)) : {linear integer_free A -> A^z}).

Lemma presentation_basis x : presentation (free_basis [the pzRingType of (int : Type)] x) = x.
Proof. exact: free_lift_basis. Qed.

Definition relation_subspace : module_subspace (rational_free A)^z.
Proof.
refine (@ModuleSubspace int (rational_free A)^z
  (fun y => exists a : integer_free A, presentation a = 0 /\ free_cast a = y) _ _ _).
- exists 0; by rewrite linear0 linear0.
- move=> y z [a [ha <-]] [b [hb <-]]; exists (a + b); split.
  + by rewrite linearD ha hb addr0.
  + exact: linearD.
- move=> r y [a [ha <-]]; exists (r *: a); split.
  + by rewrite linearZ /= ha scaler0.
  + exact: linearZ.
Defined.

Definition envelope : lmodType int :=
  [the lmodType int of module_quotient relation_subspace].

Definition embedding (x : A) : envelope :=
  quotient_pi relation_subspace (free_cast (free_basis [the pzRingType of (int : Type)] x)).

Lemma embedding_additive : additive embedding.
Proof.
move=> x y; rewrite /embedding -raddfB.
apply/eqP; rewrite quotient_pi_eq; apply/subspace_predP.
exists (free_basis [the pzRingType of (int : Type)] (x - y) -
  (free_basis [the pzRingType of (int : Type)] x - free_basis [the pzRingType of (int : Type)] y)); split.
- by rewrite ![presentation (_ - _)]linearB !presentation_basis subrr.
- by rewrite linearB /= linearB.
Qed.

HB.instance Definition _ := GRing.isAdditive.Build A envelope embedding embedding_additive.

Definition embedding_int (x : A^z) : envelope := embedding x.

Lemma embedding_int_linear : linear embedding_int.
Proof.
move=> n x y; rewrite /embedding_int raddfD.
congr (_ + _).
change (embedding (x *~ n) = n *: embedding x).
rewrite raddfMz /=.
have hs := @scaler_int int envelope n (embedding x).
by rewrite intz in hs; exact: esym hs.
Qed.

HB.instance Definition _ := GRing.isLinear.Build int A^z envelope
  _ embedding_int embedding_int_linear.

Lemma embedding_injective : injective embedding.
Proof.
move=> x y h.
have hrel : relation_subspace
    (free_cast (free_basis [the pzRingType of (int : Type)] x) -
     free_cast (free_basis [the pzRingType of (int : Type)] y)).
  apply/subspace_predP; rewrite -quotient_pi_eq; exact/eqP.
have [a [ha heq]] := hrel.
have hz : a = free_basis [the pzRingType of (int : Type)] x - free_basis [the pzRingType of (int : Type)] y.
  apply: free_cast_injective; by rewrite linearB.
rewrite hz linearB !presentation_basis in ha.
by apply/eqP; rewrite -subr_eq0; apply/eqP.
Qed.

Lemma embedding_int_injective : injective embedding_int.
Proof. exact: embedding_injective. Qed.

Theorem envelope_divisible (n : nat) (x : envelope) :
  (0 < n)%N -> exists y : envelope, y *+ n = x.
Proof.
move=> hn; have [a <-] := @quotient_pi_surjective int (rational_free A)^z relation_subspace x.
exists (quotient_pi relation_subspace ((n%:R : rat)^-1 *: (a : rational_free A))).
rewrite -raddfMn.
have hn0 : (n%:R : rat) != 0 by rewrite pnatr_eq0 -lt0n.
have heq : (((n%:R : rat)^-1 *: (a : rational_free A)) *+ n) = a.
  by rewrite -scaler_nat scalerA mulrV // scale1r.
by rewrite heq.
Qed.

End Envelope.
End DiazParkRationalEnvelope.














