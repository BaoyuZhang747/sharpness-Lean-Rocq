(** The induced boundary is the Yoneda transpose of the actual category-bar
    differential. Its exact Hom formula proves square-zero without a new
    combinatorial face calculation. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  CategoryModuleLinear ModuleDiagrams BarComplex BarNaturality BarPaths BarFreeModule
  HomologicalComplex BarResolutionHom.
From DiazParkV16b Require Import CategoryInducedBarTerms CategoryInducedBarHom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarComplex DiazParkBarNaturality DiazParkBarPaths
  DiazParkFreeModule DiazParkHomological DiazParkBarResolutionHom.
Local Open Scope ring_scope.

Section Differential.
Variable R : pzRingType.
Variables C D : category.
Variable q : functor C D.

Lemma induced_bar_postcompose {M N : module_codiagram R D}
    (u : nat_trans M N) n (a : nat_trans (induced_bar_term R q n) M) :
    induced_bar_to_cochain q (nat_comp a u) =
    bar_map_at (nat_whisker_left (functor_op q) u) (induced_bar_to_cochain q a).
Proof. reflexivity. Qed.

Definition induced_bar_boundary n :
    nat_trans (induced_bar_term R q n.+1) (induced_bar_term R q n) :=
  induced_bar_from_cochain q
    (bar_d (functor_comp (functor_op q) (induced_bar_term R q n)) n
      (induced_bar_to_cochain q (nat_id (induced_bar_term R q n)))).

Lemma induced_bar_to_cochain_boundary n {M : module_codiagram R D}
    (a : nat_trans (induced_bar_term R q n) M) :
    induced_bar_to_cochain q (nat_comp (induced_bar_boundary n) a) =
      bar_d (functor_comp (functor_op q) M) n (induced_bar_to_cochain q a).
Proof.
rewrite induced_bar_postcompose /induced_bar_boundary induced_bar_cochain_inverse.
rewrite -bar_map_d.
reflexivity.
Qed.

Lemma induced_bar_zero_cochain n (M : module_codiagram R D) :
    induced_bar_to_cochain q (diagram_zero (induced_bar_term R q n) M) = 0.
Proof. reflexivity. Qed.

Theorem induced_bar_boundary_squared n :
    nat_comp (induced_bar_boundary n.+1) (induced_bar_boundary n) =
      diagram_zero (induced_bar_term R q n.+2) (induced_bar_term R q n).
Proof.
apply (@induced_bar_to_cochain_injective R C D q (induced_bar_term R q n) n.+2).
rewrite induced_bar_to_cochain_boundary /induced_bar_boundary
  induced_bar_cochain_inverse bar_d_squared induced_bar_zero_cochain.
reflexivity.
Qed.

Lemma induced_bar_boundary_squared_apply n d
    (v : fobj (induced_bar_term R q n.+2) d) :
    module_hom_fun (component (induced_bar_boundary n) d)
      (module_hom_fun (component (induced_bar_boundary n.+1) d) v) = 0.
Proof.
exact (congr1 (fun a : nat_trans (induced_bar_term R q n.+2)
  (induced_bar_term R q n) => module_hom_fun (component a d) v)
  (induced_bar_boundary_squared n)).
Qed.

Lemma induced_bar_boundary_generator n d (s : induced_bar_basis q n.+1 d) :
    module_hom_fun (component (induced_bar_boundary n) d) (free_basis R s) =
    induced_bar_generator_value
      (bar_d (functor_comp (functor_op q) (induced_bar_term R q n)) n
        (induced_bar_to_cochain q (nat_id (induced_bar_term R q n)))) s.
Proof. exact: induced_bar_from_cochain_basis. Qed.
End Differential.

Arguments induced_bar_boundary R {C D} q n.
