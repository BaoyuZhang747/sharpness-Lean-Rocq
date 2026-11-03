From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear CategoryModuleProducts
  BarPaths BarCofaces BarFreeModule BarComplex BarResolutionTerms
  BarResolutionHom BarResolutionFaces BarResolutionDifferential.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkBarCofaces DiazParkFreeModule
  DiazParkBarComplex DiazParkBarResolutionTerms DiazParkBarResolutionHom
  DiazParkBarResolutionFaces DiazParkBarResolutionDifferential.
Local Open Scope ring_scope.

Module DiazParkBarResolutionComparison.
Section Comparison.
Variable R : pzRingType.
Variable C : category.
Variable D : module_codiagram R C.

Definition bar_evaluation n (x : C) (p : path_from (C := C) n x) :
    {linear bar_term D n -> fobj D x} :=
  (module_hom_to_linear (module_product_projection (fun _ : path_from (C := C) n x => fobj D x) p) \o
    module_hom_to_linear (module_product_projection
      (fun x : C => module_product_type (fun _ : path_from (C := C) n x => fobj D x)) x) :
    {linear bar_term D n -> fobj D x}).

Lemma term_cochain_face_constructed n i (a : bar_term D n) :
  term_to_cochain (nat_comp (@resolution_face R C n i) (cochain_to_term a)) =
    @bar_coface R C D n i a.
Proof.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (module_hom_fun (component (cochain_to_term a) x)
  (free_map R (@path_inner_face C n.+1 i x)
    (free_basis R (existT _ x (@identity C x, p)))) =
  @bar_coface R C D n i a x p).
rewrite free_map_basis cochain_to_term_basis.
case: i => [|i].
- case: p => y [f q].
  by rewrite /cochain_on_generator /= compose_id_left.
- change (@bar_action R C D x x (@identity C x)
    (a x (@path_inner_face C n i x p)) = a x (@path_inner_face C n i x p)).
  have h := fmap_id D x.
  exact: (congr1 (fun k => module_hom_fun k (a x (@path_inner_face C n i x p))) h).
Qed.

Lemma term_cochain_face n i (alpha : nat_trans (@resolution_term R C n) D) :
  term_to_cochain (nat_comp (@resolution_face R C n i) alpha) =
    @bar_coface R C D n i (term_to_cochain alpha).
Proof.
rewrite -[alpha in LHS](cochain_term_inverse alpha).
exact: term_cochain_face_constructed.
Qed.

(** Under the actual natural-map/cochain bijection, precomposition with the
    projective resolution boundary is exactly the already constructed bar
    differential, in every degree. *)
Theorem term_cochain_differential n
    (alpha : nat_trans (@resolution_term R C n) D) :
  term_to_cochain (nat_comp (@resolution_boundary R C n) alpha) =
    bar_d D n (term_to_cochain alpha).
Proof.
apply functional_extensionality_dep => x.
apply functional_extensionality_dep => p.
change (module_hom_to_linear (component alpha x)
    (@resolution_boundary_fun R C n x
      (free_basis R (existT _ x (@identity C x, p)))) =
  @bar_evaluation n.+1 x p (bar_d D n (term_to_cochain alpha))).
rewrite /resolution_boundary_fun bar_d_formula !linear_sum.
apply: eq_bigr => i _; rewrite !linearZ.
have h := term_cochain_face i alpha.
exact: (congr1 (fun a : bar_term D n.+1 => (-1) ^+ i *: a x p) h).
Qed.

End Comparison.
End DiazParkBarResolutionComparison.
