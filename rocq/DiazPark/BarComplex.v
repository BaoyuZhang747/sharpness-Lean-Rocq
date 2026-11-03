From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleProducts
  HomologicalComplex BarPaths BarCofaces BarAlternating.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory DiazParkHomological DiazParkBarPaths
  DiazParkBarCofaces DiazParkBarAlternating.
Local Open Scope ring_scope.

(** The actual, all-degree category-bar cochain complex of an arbitrary
    contravariant diagram of modules.  Categories and module values are not
    assumed finite.  Its comparison with derived limits remains separate. *)
Module DiazParkBarComplex.

Section CategoryBar.
Variable R : pzRingType.
Variable C : category.
Variable D : module_codiagram R C.

Definition bar_term n : lmodType R :=
  module_product_type (fun x : C =>
    module_product_type (fun _ : path_from n x => fobj D x)).

Definition bar_action x y (f : hom C x y) : fobj D y -> fobj D x :=
  module_hom_fun (fmap D f).

Lemma bar_action_compose x y z (f : hom C x y) (g : hom C y z)
    (v : fobj D z) :
  bar_action (compose f g) v = bar_action f (bar_action g v).
Proof.
have h := fmap_compose D (x := z) (y := y) (z := x) g f.
exact: (congr1 (fun k => module_hom_fun k v) h).
Qed.

Definition bar_coface n i (a : bar_term n) : bar_term n.+1 :=
  @raw_coface C (fun x => fobj D x) (@bar_action) n i a.

Arguments bar_coface _ _ _ : clear implicits.

Lemma bar_coface_linear n i : linear (bar_coface n i).
Proof.
move=> r a b; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
case: i => [|i].
- case: p => y [f q]. exact: module_hom_linear.
- reflexivity.
Qed.

Arguments bar_coface_linear n i : clear implicits.

HB.instance Definition _ n i :=
  GRing.isLinear.Build R (bar_term n) (bar_term n.+1) _
    (bar_coface n i) (bar_coface_linear n i).

Lemma bar_coface_identity n i j (a : bar_term n) :
  (i <= j)%N -> (j < n.+2)%N ->
  bar_coface n.+1 i (bar_coface n j a) =
    bar_coface n.+1 j.+1 (bar_coface n i a).
Proof.
move=> /leP hij hj.
have hj' : (j <= n.+1)%coq_nat by apply/leP; exact: hj.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
exact: (@raw_coface_identity C (fun x => fobj D x) (@bar_action)
  (@bar_action_compose) n i j a x p hij hj').
Qed.

Definition bar_complex : @cochain_complex R :=
  @cosimplicial_complex R bar_term
    (fun n i => (bar_coface n i : {linear bar_term n -> bar_term n.+1}))
    (@bar_coface_identity).

Definition bar_d n : {linear bar_term n -> bar_term n.+1} :=
  cochain_d bar_complex n.

Theorem bar_d_squared n (a : bar_term n) : bar_d n.+1 (bar_d n a) = 0.
Proof. exact (@cochain_d2 R bar_complex n a). Qed.

Lemma bar_d_formula n (a : bar_term n) :
  bar_d n a = \sum_(i < n.+2) (-1) ^+ i *: bar_coface n i a.
Proof. reflexivity. Qed.

End CategoryBar.
End DiazParkBarComplex.
