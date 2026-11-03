(** The literal augmentation of the induced category bar sends every basis
    string to one. Evaluation is an ordinary downward chain complex. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  CategoryDiagramHomLimit ModuleDiagrams BarComplex BarFreeModule BarPaths
  HomologicalComplex BarResolutionHom.
From DiazParkV16b Require Import ChainComplex CategoryInducedBarTerms
  CategoryInducedBarHom CategoryInducedBarDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarComplex DiazParkFreeModule DiazParkBarPaths
  DiazParkHomological DiazParkBarResolutionHom DPChainComplex.
Local Open Scope ring_scope.

Section Evaluation.
Variable R : pzRingType.
Variables C D : category.
Variable q : functor C D.

Definition induced_bar_evaluation_chain (d : D) : chain_complex R :=
  @ChainComplex R (fun n => fobj (induced_bar_term R q n) d)
    (fun n => module_hom_to_linear (component (induced_bar_boundary R q n) d))
    (fun n v => @induced_bar_boundary_squared_apply R C D q n d v).
End Evaluation.

Section Augmentation.
Variable R : comPzRingType.
Variables C D : category.
Variable q : functor C D.

Definition induced_bar_augmentation : nat_trans (induced_bar_term R q 0%N)
    (constant_regular_diagram R (opposite D)) :=
  @induced_bar_from_cochain R C D q (constant_regular_diagram R (opposite D)) 0%N
    (fun (_ : C) (_ : @path_from C 0%N _) => (1 : R^o)).

Lemma induced_bar_augmentation_basis d (s : induced_bar_basis q 0%N d) :
    module_hom_fun (component induced_bar_augmentation d) (free_basis R s) = 1.
Proof.
destruct s as [[c t] f].
rewrite /induced_bar_augmentation induced_bar_from_cochain_basis.
reflexivity.
Qed.

Theorem induced_bar_augmentation_boundary :
    nat_comp (induced_bar_boundary R q 0%N) induced_bar_augmentation =
    diagram_zero (induced_bar_term R q 1%N) (constant_regular_diagram R (opposite D)).
Proof.
apply (@induced_bar_to_cochain_injective R C D q
  (constant_regular_diagram R (opposite D)) 1%N).
rewrite induced_bar_to_cochain_boundary /induced_bar_augmentation
  induced_bar_cochain_inverse induced_bar_zero_cochain bar_d_formula.
apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intros [e [f t]].
rewrite !big_ord_recl big_ord0 /=.
change ((-1 : R) ^+ 0 *: (1 : R^o) +
  ((-1 : R) ^+ 1 *: (1 : R^o) + 0) = 0).
by rewrite expr0 expr1 scale1r scaleN1r addr0 subrr.
Qed.

Lemma induced_bar_augmentation_boundary_apply d
    (v : fobj (induced_bar_term R q 1%N) d) :
    module_hom_fun (component induced_bar_augmentation d)
      (module_hom_fun (component (induced_bar_boundary R q 0%N) d) v) = 0.
Proof.
exact (congr1 (fun a : nat_trans (induced_bar_term R q 1%N)
  (constant_regular_diagram R (opposite D)) => module_hom_fun (component a d) v)
  induced_bar_augmentation_boundary).
Qed.
End Augmentation.

Arguments induced_bar_evaluation_chain R {C D} q d.
Arguments induced_bar_augmentation R {C D} q.
