From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  BarPaths BarFreeModule BarResolutionTerms BarResolutionFaces BarAlternating.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule
  DiazParkBarResolutionTerms DiazParkBarResolutionFaces DiazParkBarAlternating.
Local Open Scope ring_scope.

Module DiazParkBarResolutionDifferential.

Section Differential.
Variable R : pzRingType.
Variable C : category.

Definition resolution_face_linear n i (x : C) :
    {linear resolution_term_obj (C := C) R n.+1 x -> resolution_term_obj (C := C) R n x} :=
  module_hom_to_linear (component (@resolution_face R C n i) x).

Definition resolution_boundary_fun n (x : C)
    (a : resolution_term_obj (C := C) R n.+1 x) : resolution_term_obj (C := C) R n x :=
  \sum_(i < n.+2) (-1) ^+ i *: resolution_face_linear n i x a.

Arguments resolution_boundary_fun n x a : clear implicits.

Lemma resolution_boundary_linear n (x : C) : linear (resolution_boundary_fun n x).
Proof.
move=> r a b; rewrite /resolution_boundary_fun scaler_sumr -big_split.
apply: eq_bigr => i _.
by rewrite linearP scalerDr !scalerA commr_sign.
Qed.

Arguments resolution_boundary_linear n x : clear implicits.

HB.instance Definition _ n x :=
  GRing.isLinear.Build R (resolution_term_obj (C := C) R n.+1 x)
    (resolution_term_obj (C := C) R n x) _ (resolution_boundary_fun n x)
    (resolution_boundary_linear n x).

Definition resolution_boundary (n : nat) :
    nat_trans (@resolution_term R C n.+1) (@resolution_term R C n).
Proof.
refine (@Build_nat_trans (opposite C) (module_category R)
  (@resolution_term R C n.+1) (@resolution_term R C n)
  (fun x => module_hom_of_linear
    (resolution_boundary_fun n x :
      {linear resolution_term_obj (C := C) R n.+1 x -> resolution_term_obj (C := C) R n x})) _).
move=> x y f; apply module_hom_ext => a.
change (resolution_boundary_fun n y
    (module_hom_to_linear (fmap (@resolution_term R C n.+1) f) a) =
  module_hom_to_linear (fmap (@resolution_term R C n) f)
    (resolution_boundary_fun n x a)).
rewrite /resolution_boundary_fun linear_sum.
apply: eq_bigr => i _; rewrite linearZ.
have h := naturality (@resolution_face R C n i) f.
exact: (congr1 (fun v => (-1) ^+ i *: v)
  (congr1 (fun k => module_hom_fun k a) h)).
Defined.

Theorem resolution_boundary_squared n (x : C)
    (a : resolution_term_obj (C := C) R n.+2 x) :
  resolution_boundary_fun n x (resolution_boundary_fun n.+1 x a) = 0.
Proof.
rewrite /resolution_boundary_fun.
transitivity (\sum_(j < n.+3) \sum_(i < n.+2)
  (-1) ^+ j *: ((-1) ^+ i *:
    resolution_face_linear n i x (resolution_face_linear n.+1 j x a))).
- rewrite [RHS]exchange_big.
  apply: eq_bigr => i _; rewrite linear_sum scaler_sumr.
  apply: eq_bigr => j _.
  by rewrite linearZ !scalerA (commr_sign ((-1) ^+ i) j).
- apply: (@alternating_rectangle_zero R (resolution_term_obj (C := C) R n x) n.+2
    (fun i j => resolution_face_linear n j x (resolution_face_linear n.+1 i x a))).
  move=> i j /leP hij hj.
  have hj' : (j <= n.+1)%coq_nat by apply/leP; exact: hj.
  have h := @resolution_faces R C n i j hij hj'.
  exact (congr1 (fun alpha : nat_trans (@resolution_term R C n.+2)
    (@resolution_term R C n) => module_hom_fun (component alpha x) a) h).
Qed.

End Differential.
End DiazParkBarResolutionDifferential.
