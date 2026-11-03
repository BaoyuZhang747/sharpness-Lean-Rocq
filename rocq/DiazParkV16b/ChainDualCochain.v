(** Actual Hom(-,A) cochains of arbitrary nonnegative chain complexes. *)
From mathcomp Require Import all_boot all_algebra.
From DiazPark Require Import HomologicalComplex.
From DiazParkV16b Require Import ChainComplex LinearMapSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DPChainComplex DPLinearMapSpace DiazParkHomological.
Local Open Scope ring_scope.

Module DPChainDualCochain.
Section Duality.
Variable R : comPzRingType.
Variable A : lmodType R.

Definition dual_complex (C : chain_complex R) : cochain_complex R.
Proof.
refine (@CochainComplex R (fun n => linear_maps (chain_term C n) A)
  (fun n => @precompose R (chain_term C n) A (chain_term C n.+1) (chain_d C n)) _).
move=> n f; apply ext => x.
change (as_linear f (chain_d C n (chain_d C n.+1 x)) = 0).
by rewrite chain_d2 linear0.
Defined.

Lemma dual_d_evaluate (C : chain_complex R) n
    (f : cochain_term (dual_complex C) n) x :
  evaluate (cochain_d (dual_complex C) n f) x = evaluate f (chain_d C n x).
Proof. reflexivity. Qed.

Definition dual_map (C D : chain_complex R) (f : chain_map C D) :
    cochain_map (dual_complex D) (dual_complex C).
Proof.
refine (@CochainMap R (dual_complex D) (dual_complex C)
  (fun n => @precompose R (chain_term D n) A (chain_term C n) (chain_map_at f n)) _).
move=> n a; apply ext => x.
change (evaluate a (chain_map_at f n (chain_d C n x)) =
  evaluate a (chain_d D n (chain_map_at f n.+1 x))).
by rewrite chain_map_commutes.
Defined.

Lemma dual_map_evaluate (C D : chain_complex R) (f : chain_map C D)
    n (a : cochain_term (dual_complex D) n) x :
  evaluate (cochain_map_at (dual_map f) n a) x = evaluate a (chain_map_at f n x).
Proof. reflexivity. Qed.

Lemma dual_identity_at (C : chain_complex R) n
    (a : cochain_term (dual_complex C) n) :
  cochain_map_at (dual_map (chain_identity C)) n a = a.
Proof. by apply ext => x. Qed.

Lemma dual_composition_at (C D E : chain_complex R)
    (f : chain_map C D) (g : chain_map D E) n
    (a : cochain_term (dual_complex E) n) :
  cochain_map_at (dual_map (chain_composition f g)) n a =
    cochain_map_at (dual_map f) n (cochain_map_at (dual_map g) n a).
Proof. by apply ext => x. Qed.

Definition dual_homotopy (C D : chain_complex R) (f g : chain_map C D)
    (h : chain_homotopy f g) : cochain_homotopy (dual_map f) (dual_map g).
Proof.
refine (@CochainHomotopy R (dual_complex D) (dual_complex C)
  (dual_map f) (dual_map g)
  (fun n => @precompose R (chain_term D n.+1) A (chain_term C n) (chain_homotopy_at h n)) _ _).
- move=> a; apply ext => x.
  change (as_linear a (chain_map_at f 0%N x) - as_linear a (chain_map_at g 0%N x) =
    as_linear a (chain_d D 0%N (chain_homotopy_at h 0%N x))).
  by rewrite chain_homotopy_zero linearB.
- move=> n a; apply ext => x.
  change (as_linear a (chain_map_at f n.+1 x) - as_linear a (chain_map_at g n.+1 x) =
    as_linear a (chain_homotopy_at h n (chain_d C n x)) +
    as_linear a (chain_d D n.+1 (chain_homotopy_at h n.+1 x))).
  rewrite -linearB -linearD
    (addrC (chain_homotopy_at h n (chain_d C n x))).
  by rewrite (@chain_homotopy_succ R C D f g h n x).
Defined.

End Duality.

Section Coefficients.
Variable R : comPzRingType.
Variable A : lmodType R.

Definition coefficient_map (C : chain_complex R) (B : lmodType R)
    (f : {linear A -> B}) :
    cochain_map (@dual_complex R A C)
      (@dual_complex R B C).
Proof.
refine (@CochainMap R (@dual_complex R A C) (@dual_complex R B C)
  (fun n => @postcompose R (chain_term C n) A B f) _).
by move=> n a; apply ext => x.
Defined.

End Coefficients.
End DPChainDualCochain.
