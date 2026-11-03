From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules CategoryModuleLinear
  BarPaths BarFreeModule BarResolutionTerms BarComplex.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule
  DiazParkBarResolutionTerms DiazParkBarComplex.
Local Open Scope ring_scope.

(** The linear Yoneda calculation for every actual bar-resolution term. *)
Module DiazParkBarResolutionHom.

Lemma free_module_hom_ext (R : pzRingType) (X : Type) (V : lmodType R)
    (f g : module_hom (free_module R X) V) :
  (forall x, f (free_basis R x) = g (free_basis R x)) -> f = g.
Proof.
move=> h; apply module_hom_ext.
exact: (free_lift_ext (g := module_hom_to_linear f)
  (h := module_hom_to_linear g) h).
Qed.

Section HomCalculation.
Variable R : pzRingType.
Variable C : category.
Variable D : module_codiagram R C.

Definition term_to_cochain n (alpha : nat_trans (@resolution_term R C n) D) :
    bar_term D n :=
  fun x q => module_hom_fun (component alpha x)
    (free_basis R (existT _ x (@identity C x, q))).

Definition cochain_on_generator n (a : bar_term D n) (x : C)
    (p : path_from (C := C) n.+1 x) : fobj D x :=
  match p with
  | existT y (f, q) => @bar_action R C D x y f (a y q)
  end.

Definition cochain_to_term_component n (a : bar_term D n) (x : C) :
    module_hom (fobj (@resolution_term R C n) x) (fobj D x) :=
  module_hom_of_linear
    (free_lift (@cochain_on_generator n a x) :
      {linear free_module R (path_from (C := C) n.+1 x) -> fobj D x}).

Lemma cochain_to_term_component_basis n (a : bar_term D n) (x : C)
    (p : path_from (C := C) n.+1 x) :
  cochain_to_term_component a x (free_basis R p) = cochain_on_generator a p.
Proof. exact: free_lift_basis. Qed.

Definition cochain_to_term n (a : bar_term D n) :
    nat_trans (@resolution_term R C n) D.
Proof.
refine (@Build_nat_trans (opposite C) (module_category R)
  (@resolution_term R C n) D (@cochain_to_term_component n a) _).
move=> x y f; apply free_module_hom_ext => p.
change (cochain_to_term_component a y
    (module_hom_fun (fmap (@resolution_term R C n) f) (free_basis R p)) =
  module_hom_fun (fmap D f) (cochain_to_term_component a x (free_basis R p))).
rewrite resolution_term_map_basis !cochain_to_term_component_basis.
case: p => z [g q].
exact: (@bar_action_compose R C D y x z f g (a z q)).
Defined.

Lemma cochain_to_term_basis n (a : bar_term D n) (x : C)
    (p : path_from (C := C) n.+1 x) :
  module_hom_fun (component (cochain_to_term a) x) (free_basis R p) =
    cochain_on_generator a p.
Proof. exact: cochain_to_term_component_basis. Qed.

Lemma term_cochain_inverse n (a : bar_term D n) :
  term_to_cochain (cochain_to_term a) = a.
Proof.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => q.
change (cochain_to_term_component a x
  (free_basis R (existT _ x (@identity C x, q))) = a x q).
rewrite cochain_to_term_component_basis /cochain_on_generator /bar_action.
have h := fmap_id D x.
exact: (congr1 (fun k => module_hom_fun k (a x q)) h).
Qed.

Lemma cochain_term_inverse_component n
    (alpha : nat_trans (@resolution_term R C n) D) x :
  component (cochain_to_term (term_to_cochain alpha)) x = component alpha x.
Proof.
apply free_module_hom_ext => p.
case: p => y [f q].
rewrite cochain_to_term_basis.
have h := naturality alpha f.
have hv := congr1
  (fun k => module_hom_fun k (free_basis R (existT _ y (@identity C y, q)))) h.
change (module_hom_fun (component alpha x)
    (free_map R (@path_precompose C n x y f)
      (free_basis R (existT _ y (@identity C y, q)))) =
  module_hom_fun (fmap D f)
    (module_hom_fun (component alpha y)
      (free_basis R (existT _ y (@identity C y, q))))) in hv.
rewrite free_map_basis /path_precompose compose_id_right in hv.
exact: esym hv.
Qed.

Lemma cochain_term_inverse n (alpha : nat_trans (@resolution_term R C n) D) :
  cochain_to_term (term_to_cochain alpha) = alpha.
Proof. apply nat_trans_ext; exact: cochain_term_inverse_component. Qed.

Lemma term_to_cochain_injective n : injective (@term_to_cochain n).
Proof.
move=> alpha beta e.
rewrite -(cochain_term_inverse alpha) -(cochain_term_inverse beta).
by rewrite e.
Qed.

End HomCalculation.
End DiazParkBarResolutionHom.
