From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleProducts
  HomologicalComplex BarPaths BarCofaces BarComplex BarNaturality.
From DiazParkV16b Require Import CategoryBarPullbackPaths.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory DiazParkHomological DiazParkBarPaths DiazParkBarComplex
  DiazParkBarNaturality DPCategoryBarPullback.
Local Open Scope ring_scope.

(** Contravariant functoriality in the indexing category of the actual bar
    complex. Coefficients are arbitrary modules over any possibly-zero ring. *)
Module DPCategoryBarPullbackMaps.

Section Pullback.
Variable R : pzRingType.
Variables C D : category.
Variable F : functor C D.
Variable M : module_codiagram R D.

Definition pullback_diagram : module_codiagram R C :=
  functor_comp (functor_op F) M.

Definition bar_pullback_at n (a : bar_term M n) : bar_term pullback_diagram n :=
  fun x p => a (fobj F x) (path_map_from F n x p).

Arguments bar_pullback_at _ _ : clear implicits.

Lemma bar_pullback_at_linear n : linear (bar_pullback_at n).
Proof.
move=> r a b; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
reflexivity.
Qed.

Arguments bar_pullback_at_linear n : clear implicits.

HB.instance Definition _ n :=
  GRing.isLinear.Build R (bar_term M n) (bar_term pullback_diagram n) _
    (bar_pullback_at n) (bar_pullback_at_linear n).

Lemma bar_pullback_coface n i (a : bar_term M n) :
  bar_coface (D := pullback_diagram) i (bar_pullback_at n a) =
    bar_pullback_at n.+1 (bar_coface (D := M) i a).
Proof.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
case: i => [|i].
- case: p => y [f q]. reflexivity.
- change (a (fobj F x) (path_map_from F n x (@path_inner_face C n i x p)) =
    a (fobj F x) (@path_inner_face D n i (fobj F x) (path_map_from F n.+1 x p))).
  by rewrite path_map_inner_face.
Qed.

Lemma bar_pullback_d n (a : bar_term M n) :
  bar_d pullback_diagram n (bar_pullback_at n a) =
    bar_pullback_at n.+1 (bar_d M n a).
Proof.
rewrite !bar_d_formula linear_sum.
apply: eq_bigr => i _; rewrite linearZ.
by rewrite bar_pullback_coface.
Qed.

Definition bar_pullback_cochain_map :
    cochain_map (bar_complex M) (bar_complex pullback_diagram) :=
  @CochainMap R (bar_complex M) (bar_complex pullback_diagram)
    (fun n => (bar_pullback_at n : {linear bar_term M n -> bar_term pullback_diagram n}))
    (@bar_pullback_d).

Lemma bar_pullback_cochain_map_at n (a : bar_term M n) x (p : @path_from C n x) :
  cochain_map_at bar_pullback_cochain_map n a x p =
    a (fobj F x) (path_map_from F n x p).
Proof. reflexivity. Qed.

End Pullback.

Arguments pullback_diagram {R C D} F M.
Arguments bar_pullback_at {R C D} F M n a.
Arguments bar_pullback_cochain_map {R C D} F M.

Lemma bar_pullback_identity (R : pzRingType) (C : category)
    (M : module_codiagram R C) n (a : bar_term M n) :
  bar_pullback_at (functor_id C) M n a = a.
Proof.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (a x (path_map_from (functor_id C) n x p) = a x p).
by rewrite path_map_from_identity.
Qed.

Lemma bar_pullback_composition (R : pzRingType) (C D E : category)
    (F : functor C D) (G : functor D E) (M : module_codiagram R E)
    n (a : bar_term M n) :
  bar_pullback_at (functor_comp F G) M n a =
    bar_pullback_at F (pullback_diagram G M) n (bar_pullback_at G M n a).
Proof.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (a (fobj G (fobj F x)) (path_map_from (functor_comp F G) n x p) =
    a (fobj G (fobj F x)) (path_map_from G n (fobj F x) (path_map_from F n x p))).
by rewrite path_map_from_composition.
Qed.

Lemma bar_pullback_coefficient_naturality (R : pzRingType) (C D : category)
    (F : functor C D) (M N : module_codiagram R D) (alpha : nat_trans M N)
    n (a : bar_term M n) :
  bar_pullback_at F N n (bar_map_at alpha a) =
    bar_map_at (nat_whisker_left (functor_op F) alpha) (bar_pullback_at F M n a).
Proof. reflexivity. Qed.

End DPCategoryBarPullbackMaps.
