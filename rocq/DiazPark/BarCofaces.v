From Stdlib Require Import Arith.PeanoNat.
From DiazPark Require Import Category BarPaths.

Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import DiazParkBarPaths.

(** The category-specific cofaces with contravariant coefficients.  Their
    pointwise identities need only the composition law of the coefficient
    action; module linearity is a subsequent, separate packaging step. *)
Module DiazParkBarCofaces.

Section Cofaces.
Variable C : category.
Variable D : C -> Type.
Variable action : forall {x y}, hom C x y -> D y -> D x.
Hypothesis action_compose : forall x y z (f : hom C x y)
    (g : hom C y z) (v : D z),
  action (compose f g) v = action f (action g v).

Definition raw_cochains n := forall x : C, path_from n x -> D x.

Definition raw_coface n i (a : raw_cochains n) : raw_cochains (S n) :=
  fun x p =>
    match i with
    | 0 =>
        match p with
        | existT _ y (f, q) => action f (a y q)
        end
    | S j => a x (@path_inner_face C n j x p)
    end.

Arguments raw_cochains _ : clear implicits.
Arguments raw_coface _ _ _ _ _ : clear implicits.

Theorem raw_coface_identity n i j (a : raw_cochains n) x
    (p : path_from (S (S n)) x) :
  i <= j -> j <= S n ->
  raw_coface (S n) i (raw_coface n j a) x p =
    raw_coface (S n) (S j) (raw_coface n i a) x p.
Proof.
  intros hij hj. destruct i as [|i], j as [|j].
  - destruct p as [y [f [z [g q]]]].
    simpl. symmetry. apply action_compose.
  - destruct p as [y [f q]]. reflexivity.
  - inversion hij.
  - unfold raw_coface.
    rewrite (path_inner_faces p (proj2 (Nat.succ_le_mono _ _) hij)
      (proj2 (Nat.succ_le_mono _ _) hj)). reflexivity.
Qed.

Section CoefficientMaps.
Variable E : C -> Type.
Variable actionE : forall {x y}, hom C x y -> E y -> E x.
Variable component : forall x, D x -> E x.
Arguments component _ _ : clear implicits.
Hypothesis component_natural : forall x y (f : hom C x y) (v : D y),
  component x (action f v) = actionE f (component y v).

Definition raw_cochain_map n (a : raw_cochains n) :
    forall x, path_from n x -> E x :=
  fun x p => component x (a x p).

Arguments raw_cochain_map {n} a x p.

Lemma raw_coface_naturality n i (a : raw_cochains n) x
    (p : path_from (S n) x) :
  raw_cochain_map (raw_coface n i a) x p =
    match i with
    | 0 =>
        match p with
        | existT _ y (f, q) => actionE f (raw_cochain_map a y q)
        end
    | S j => raw_cochain_map a x (@path_inner_face C n j x p)
    end.
Proof.
  destruct i as [|i].
  - destruct p as [y [f q]]. apply component_natural.
  - reflexivity.
Qed.

End CoefficientMaps.
End Cofaces.
End DiazParkBarCofaces.
