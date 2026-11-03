From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules BarPaths BarFreeModule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory DiazParkBarPaths DiazParkFreeModule.
Local Open Scope ring_scope.

(** The actual diagram terms of the augmented projective bar resolution.
    At Y, degree n is free on strings Y -> x_0 -> ... -> x_n. *)
Module DiazParkBarResolutionTerms.

Section Terms.
Variable R : pzRingType.
Variable C : category.

Definition path_precompose n x y (f : hom C x y)
    (p : path_from n.+1 y) : path_from n.+1 x :=
  match p with
  | existT z (g, q) => existT _ z (compose f g, q)
  end.

Lemma path_precompose_identity n x (p : path_from n.+1 x) :
  path_precompose (identity x) p = p.
Proof. case: p => y [f q]; by rewrite /path_precompose compose_id_left. Qed.

Lemma path_precompose_composition n x y z (f : hom C x y) (g : hom C y z)
    (p : path_from n.+1 z) :
  path_precompose (compose f g) p = path_precompose f (path_precompose g p).
Proof. case: p => w [h q]; by rewrite /path_precompose compose_assoc. Qed.

Definition resolution_term_obj n (x : C) : lmodType R :=
  free_module R (path_from n.+1 x).

Definition resolution_term (n : nat) : module_codiagram R C.
Proof.
refine (@Build_functor (opposite C) (module_category R)
  (resolution_term_obj n)
  (fun x y f => module_hom_of_linear (free_map R (@path_precompose n y x f))) _ _).
- move=> x; apply module_hom_ext => a.
  change (free_map R (@path_precompose n x x (identity x)) a = a).
  have hi : @path_precompose n x x (identity x) = idfun.
    apply functional_extensionality_dep; exact: path_precompose_identity.
  by rewrite hi free_map_identity.
- move=> x y z f g; apply module_hom_ext => a.
  change (free_map R (@path_precompose n z x (@compose C z y x g f)) a =
    free_map R (@path_precompose n z y g)
      (free_map R (@path_precompose n y x f) a)).
  rewrite -free_map_composition.
  have hc : @path_precompose n z x (@compose C z y x g f) =
      @path_precompose n z y g \o @path_precompose n y x f.
    apply functional_extensionality_dep; exact: path_precompose_composition.
  by rewrite hc.
Defined.

Lemma resolution_term_map_basis n x y (f : hom C x y)
    (p : path_from n.+1 y) :
  module_hom_fun (fmap (resolution_term n) f) (free_basis R p) =
    free_basis R (path_precompose f p).
Proof. exact: free_map_basis. Qed.

End Terms.
End DiazParkBarResolutionTerms.
