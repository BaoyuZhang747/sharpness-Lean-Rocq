From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleProducts
  HomologicalComplex BarPaths BarComplex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory DiazParkHomological DiazParkBarPaths DiazParkBarComplex.
Local Open Scope ring_scope.

(** Coefficient maps on the actual category-bar complex, with the differential
    naturality proved from the natural transformation's commuting squares. *)
Module DiazParkBarNaturality.

Section CoefficientMap.
Variable R : pzRingType.
Variable C : category.
Variables D E : module_codiagram R C.
Variable alpha : nat_trans D E.

Definition bar_map_at n (a : bar_term D n) : bar_term E n :=
  fun x p => module_hom_fun (component alpha x) (a x p).

Arguments bar_map_at _ _ : clear implicits.

Lemma bar_map_at_linear n : linear (bar_map_at n).
Proof.
move=> r a b; apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
exact: module_hom_linear.
Qed.

Arguments bar_map_at_linear n : clear implicits.

HB.instance Definition _ n :=
  GRing.isLinear.Build R (bar_term D n) (bar_term E n) _
    (bar_map_at n) (bar_map_at_linear n).

Lemma bar_map_coface n i (a : bar_term D n) :
  bar_coface (D := E) i (bar_map_at n a) =
    bar_map_at n.+1 (bar_coface (D := D) i a).
Proof.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
case: i => [|i].
- case: p => y [f q].
  have h := naturality alpha f.
  symmetry.
  exact (congr1 (fun k => module_hom_fun k (a y q)) h).
- reflexivity.
Qed.

Lemma bar_map_d n (a : bar_term D n) :
  bar_d E n (bar_map_at n a) = bar_map_at n.+1 (bar_d D n a).
Proof.
rewrite !bar_d_formula linear_sum.
apply: eq_bigr => i _; rewrite linearZ.
by rewrite bar_map_coface.
Qed.

Definition bar_cochain_map : cochain_map (bar_complex D) (bar_complex E) :=
  @CochainMap R (bar_complex D) (bar_complex E)
    (fun n => (bar_map_at n : {linear bar_term D n -> bar_term E n}))
    (@bar_map_d).

Lemma bar_cochain_map_at n (a : bar_term D n) x (p : path_from n x) :
  cochain_map_at bar_cochain_map n a x p =
    module_hom_fun (component alpha x) (a x p).
Proof. reflexivity. Qed.

End CoefficientMap.

Section FunctorLaws.
Variable R : pzRingType.
Variable C : category.
Variables D E F : module_codiagram R C.

Lemma bar_map_identity n (a : bar_term D n) :
  bar_map_at (nat_id D) a = a.
Proof. reflexivity. Qed.

Lemma bar_map_composition (alpha : nat_trans D E) (beta : nat_trans E F)
    n (a : bar_term D n) :
  bar_map_at (nat_comp alpha beta) a = bar_map_at beta (bar_map_at alpha a).
Proof. reflexivity. Qed.

End FunctorLaws.
End DiazParkBarNaturality.
