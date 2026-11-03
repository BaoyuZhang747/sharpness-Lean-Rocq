(** Actual Yoneda calculation: Hom from an induced free bar term is the
    ordinary bar cochain term after restriction along q.op. *)
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  BarPaths BarFreeModule BarComplex BarResolutionHom.
From DiazParkV16b Require Import CategoryInducedBarTerms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule DiazParkBarComplex
  DiazParkBarResolutionHom.
Local Open Scope ring_scope.

Section HomCalculation.
Variable R : pzRingType.
Variables C D : category.
Variable q : functor C D.
Variable M : module_codiagram R D.

Definition induced_bar_to_cochain n (a : nat_trans (induced_bar_term R q n) M) :
    bar_term (functor_comp (functor_op q) M) n :=
  fun c s => module_hom_fun (component a (fobj q c))
    (free_basis R (existT _ (existT _ c s) (identity (fobj q c)))).

Definition induced_bar_generator_value n
    (a : bar_term (functor_comp (functor_op q) M) n) d
    (s : induced_bar_basis q n d) : fobj M d :=
  match s with
  | existT (existT c t) f => module_hom_fun (fmap M f) (a c t)
  end.

Definition induced_bar_from_cochain_component n
    (a : bar_term (functor_comp (functor_op q) M) n) d :
    module_hom (fobj (induced_bar_term R q n) d) (fobj M d) :=
  module_hom_of_linear (free_lift (@induced_bar_generator_value n a d) :
    {linear free_module R (induced_bar_basis q n d) -> fobj M d}).

Lemma induced_bar_from_cochain_basis n
    (a : bar_term (functor_comp (functor_op q) M) n) d (s : induced_bar_basis q n d) :
    induced_bar_from_cochain_component a d (free_basis R s) =
    induced_bar_generator_value a s.
Proof. exact: free_lift_basis. Qed.

Definition induced_bar_from_cochain n
    (a : bar_term (functor_comp (functor_op q) M) n) :
    nat_trans (induced_bar_term R q n) M.
Proof.
refine (@Build_nat_trans (opposite D) (module_category R)
  (induced_bar_term R q n) M (@induced_bar_from_cochain_component n a) _).
intros d e f; apply free_module_hom_ext; intros [[c s] g].
change (induced_bar_from_cochain_component a e
  (module_hom_fun (fmap (induced_bar_term R q n) f)
    (free_basis R (existT _ (existT _ c s) g))) =
  module_hom_fun (fmap M f)
    (induced_bar_from_cochain_component a d (free_basis R (existT _ (existT _ c s) g)))).
rewrite induced_bar_term_map_basis !induced_bar_from_cochain_basis.
exact (congr1 (fun k : module_hom (fobj M (fobj q c)) (fobj M e) => k (a c s))
  (@fmap_compose (opposite D) (module_category R) M (fobj q c) d e g f)).
Defined.

Lemma induced_bar_cochain_inverse n (a : bar_term (functor_comp (functor_op q) M) n) :
    induced_bar_to_cochain (induced_bar_from_cochain a) = a.
Proof.
apply functional_extensionality_dep; intro c.
apply functional_extensionality_dep; intro s.
change (induced_bar_from_cochain_component a (fobj q c)
  (free_basis R (existT _ (existT _ c s) (identity (fobj q c)))) = a c s).
rewrite induced_bar_from_cochain_basis.
exact (congr1 (fun k : module_hom (fobj M (fobj q c)) (fobj M (fobj q c)) => k (a c s))
  (fmap_id M (fobj q c))).
Qed.

Lemma induced_bar_term_inverse n (a : nat_trans (induced_bar_term R q n) M) :
    induced_bar_from_cochain (induced_bar_to_cochain a) = a.
Proof.
apply nat_trans_ext; intro d; apply free_module_hom_ext; intros [[c s] f].
rewrite induced_bar_from_cochain_basis.
have h := naturality a f.
have hv := congr1 (fun k => module_hom_fun k
  (free_basis R (existT _ (existT _ c s) (identity (fobj q c))))) h.
change (module_hom_fun (component a d)
  (free_map R (@induced_bar_precompose C D q n d (fobj q c) f)
    (free_basis R (existT _ (existT _ c s) (identity (fobj q c))))) =
  module_hom_fun (fmap M f)
    (module_hom_fun (component a (fobj q c))
      (free_basis R (existT _ (existT _ c s) (identity (fobj q c)))))) in hv.
rewrite free_map_basis /induced_bar_precompose compose_id_right in hv.
exact: esym hv.
Qed.

Lemma induced_bar_to_cochain_injective n : injective (@induced_bar_to_cochain n).
Proof.
intros a b h; rewrite -(induced_bar_term_inverse a) -(induced_bar_term_inverse b).
by rewrite h.
Qed.
End HomCalculation.

Arguments induced_bar_to_cochain {R C D} q {M n} a.
Arguments induced_bar_from_cochain {R C D} q {M n} a.
