(** Multiplying a cochain differential by (-1)^p gives an actually isomorphic
    complex. The degree-n isomorphism is multiplication by (-1)^(p*n).
    Centrality of the sign is proved, so the ring need not be commutative. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  HomologicalComplex CategoryComplexIso.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological.
Local Open Scope ring_scope.

Module DPCochainSignTwist.
Section Signs.
Variable R : pzRingType.

Definition sign_map (V : lmodType R) p (x : V) : V := (-1 : R)^+p *: x.
Lemma sign_map_linear (V : lmodType R) p : linear (@sign_map V p).
Proof. intros a x y; by rewrite /sign_map scalerDr !scalerA commr_sign. Qed.
HB.instance Definition _ (V : lmodType R) p := GRing.isLinear.Build R V V _
  (@sign_map V p) (@sign_map_linear V p).

Lemma sign_map_twice (V : lmodType R) p (x : V) : sign_map p (sign_map p x) = x.
Proof. by rewrite /sign_map scalerA -expr2 exprAC expr2 mulN1r opprK expr1n scale1r. Qed.

Definition sign_iso (V : lmodType R) (p : nat) : @isomorphism (module_category R) V V.
Proof.
refine (@Build_isomorphism (module_category R) V V
  (module_hom_of_linear (@sign_map V p)) (module_hom_of_linear (@sign_map V p)) _ _).
- apply module_hom_ext; exact: sign_map_twice.
- apply module_hom_ext; exact: sign_map_twice.
Defined.

Variable K : cochain_complex R.
Variable p : nat.

Definition sign_twist_d n (x : cochain_term K n) : cochain_term K n.+1 :=
  sign_map p (cochain_d K n x).
Lemma sign_twist_d_linear n : linear (@sign_twist_d n).
Proof. intros a x y; by rewrite /sign_twist_d !linearP. Qed.
HB.instance Definition _ n := GRing.isLinear.Build R (cochain_term K n) (cochain_term K n.+1) _
  (@sign_twist_d n) (@sign_twist_d_linear n).

Lemma sign_twist_d_squared n (x : cochain_term K n) : sign_twist_d (sign_twist_d x) = 0.
Proof.
change ((-1 : R)^+p *: cochain_d K n.+1 ((-1 : R)^+p *: cochain_d K n x) = 0).
have hd : cochain_d K n.+1 ((-1 : R)^+p *: cochain_d K n x) =
  (-1 : R)^+p *: cochain_d K n.+1 (cochain_d K n x) by exact: linearZ.
rewrite hd (@cochain_d2 R K n x).
change ((-1 : R)^+p *: ((-1 : R)^+p *: (0 : cochain_term K n.+2)) = 0).
by rewrite !scaler0.
Qed.

Definition sign_twist : cochain_complex R :=
  @CochainComplex R (cochain_term K) (fun n => (@sign_twist_d n : {linear _ -> _})) sign_twist_d_squared.

Definition sign_twist_term_iso n : @isomorphism (module_category R)
    (cochain_term sign_twist n) (cochain_term K n) := sign_iso (cochain_term K n) (p*n)%N.

Lemma sign_twist_term_commutes n x :
    cochain_d K n (module_hom_fun (iso_hom (sign_twist_term_iso n)) x) =
      module_hom_fun (iso_hom (sign_twist_term_iso n.+1)) (cochain_d sign_twist n x).
Proof.
change (cochain_d K n ((-1 : R)^+(p*n)%N *: x) =
  (-1 : R)^+(p*n.+1)%N *: ((-1 : R)^+p *: cochain_d K n x)).
have hlin : cochain_d K n ((-1 : R)^+(p*n)%N *: x) =
  (-1 : R)^+(p*n)%N *: cochain_d K n x by exact: linearZ.
have hpn : (p*n.+1)%N = (p*n+p)%N by rewrite mulnS addnC.
rewrite hlin hpn exprD -scalerA.
change ((-1 : R)^+(p*n)%N *: cochain_d K n x =
  (-1 : R)^+(p*n)%N *: sign_map p (sign_map p (cochain_d K n x))).
by rewrite sign_map_twice.
Qed.

Definition sign_twist_cochain_map := term_iso_cochain_map sign_twist_term_commutes.
Definition sign_twist_cohomology_iso n := term_iso_cohomology_iso sign_twist_term_commutes n.

End Signs.
End DPCochainSignTwist.
