From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules HomologicalComplex
  BarPaths BarComplex BarNaturality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkHomological DiazParkBarPaths DiazParkBarComplex DiazParkBarNaturality.
Local Open Scope ring_scope.

(** The category-bar functor takes every pointwise short exact coefficient
    sequence to a degreewise short exact sequence of actual complexes.
    Arbitrary products are allowed; no finite-category premise is needed. *)
Module DiazParkBarExactness.
Section Exactness.
Variable R : pzRingType.
Variable C : category.
Variables A B D : module_codiagram R C.
Variables (f : nat_trans A B) (g : nat_trans B D).
Hypothesis fi : forall x, injective (module_hom_fun (component f x)).
Hypothesis fg : forall x a, module_hom_fun (component g x)
  (module_hom_fun (component f x) a) = 0.
Hypothesis fk : forall x b, module_hom_fun (component g x) b = 0 ->
  exists a, module_hom_fun (component f x) a = b.
Hypothesis gs : forall x d, exists b, module_hom_fun (component g x) b = d.

Definition bar_short_exact : degreewise_short_exact (bar_cochain_map f) (bar_cochain_map g).
Proof.
constructor.
- move=> n a b h; apply functional_extensionality_dep => x.
  apply functional_extensionality_dep => p; apply (@fi x).
  exact: (congr1 (fun v : bar_term B n => v x p) h).
- move=> n a; apply functional_extensionality_dep => x.
  apply functional_extensionality_dep => p; exact: fg.
- move=> n b hb.
  have h : forall (x : C) (p : path_from (C := C) n x),
      exists a, module_hom_fun (component f x) a = b x p.
    move=> x p; apply: (@fk x (b x p)).
    exact: (congr1 (fun v : bar_term D n => v x p) hb).
  exists (fun x p => proj1_sig (constructive_indefinite_description (h x p))).
  apply functional_extensionality_dep => x.
  apply functional_extensionality_dep => p.
  exact: (proj2_sig (constructive_indefinite_description (h x p))).
- move=> n d.
  exists (fun x p => proj1_sig (constructive_indefinite_description (@gs x (d x p)))).
  apply functional_extensionality_dep => x.
  apply functional_extensionality_dep => p.
  exact: (proj2_sig (constructive_indefinite_description (@gs x (d x p)))).
Defined.

End Exactness.
End DiazParkBarExactness.

