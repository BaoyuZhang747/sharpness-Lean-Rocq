From HB Require Import structures.
From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryModules CategoryModuleLinear
  BarPaths BarFreeModule BarResolutionTerms BarResolutionHom
  BarResolutionFaces BarResolutionDifferential.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule
  DiazParkBarResolutionTerms DiazParkBarResolutionHom
  DiazParkBarResolutionFaces DiazParkBarResolutionDifferential.
Local Open Scope ring_scope.

Module DiazParkBarResolutionAugmentation.
Section Augmentation.
Variable R : pzRingType.
Variable C : category.

Definition resolution_constant : module_codiagram R C.
Proof.
refine (@Build_functor (opposite C) (module_category R)
  (fun _ => [the lmodType R of R^o])
  (fun _ _ _ => module_hom_id [the lmodType R of R^o]) _ _).
- move=> x; reflexivity.
- move=> x y z f g; apply module_hom_ext => r; reflexivity.
Defined.

Definition resolution_augmentation_fun (x : C) :
    {linear resolution_term_obj (C := C) R 0 x -> R^o} :=
  (free_lift (fun _ : path_from (C := C) 1 x => (1 : R^o)) :
    {linear resolution_term_obj (C := C) R 0 x -> R^o}).

Lemma resolution_augmentation_basis (x : C) (p : path_from (C := C) 1 x) :
  resolution_augmentation_fun x (free_basis R p) = 1.
Proof. exact: free_lift_basis. Qed.

Definition resolution_augmentation :
    nat_trans (@resolution_term R C 0) resolution_constant.
Proof.
refine (@Build_nat_trans (opposite C) (module_category R)
  (@resolution_term R C 0) resolution_constant
  (fun x => module_hom_of_linear (resolution_augmentation_fun x)) _).
move=> x y f; apply free_module_hom_ext => p.
change (resolution_augmentation_fun y
    (free_map R (@path_precompose C 0 y x f) (free_basis R p)) =
  resolution_augmentation_fun x (free_basis R p)).
by rewrite free_map_basis !resolution_augmentation_basis.
Defined.

Lemma resolution_augmentation_boundary (x : C)
    (a : resolution_term_obj (C := C) R 1 x) :
  resolution_augmentation_fun x (@resolution_boundary_fun R C 0 x a) = 0.
Proof.
pose f : {linear resolution_term_obj (C := C) R 1 x -> R^o} :=
  (resolution_augmentation_fun x \o @resolution_boundary_fun R C 0 x :
    {linear resolution_term_obj (C := C) R 1 x -> R^o}).
change (f a = 0).
rewrite -[in LHS](free_basis_generation a) linear_sum.
apply: big1_seq => p _; rewrite linearZ.
suff hz : f (free_basis R p) = 0 by rewrite hz; exact: scaler0.
change (resolution_augmentation_fun x
  (@resolution_boundary_fun R C 0 x (free_basis R p)) = 0).
rewrite /resolution_boundary_fun !big_ord_recl big_ord0 /=.
rewrite !linearD !linearZ linear0 /resolution_face_linear.
change ((-1) ^+ 0 *:
    resolution_augmentation_fun x (free_map R (@path_inner_face C 1 0 x) (free_basis R p)) +
  ((-1) ^+ 1 *:
    resolution_augmentation_fun x (free_map R (@path_inner_face C 1 1 x) (free_basis R p)) + 0) = 0).
by rewrite !free_map_basis !resolution_augmentation_basis expr0 expr1 scale1r scaleN1r addr0 subrr.
Qed.

Definition resolution_augmentation_section_fun (x : C) (r : R^o) :
    resolution_term_obj (C := C) R 0 x :=
  (r : R) *: free_basis R (existT _ x (@identity C x, tt)).

Lemma resolution_augmentation_section_linear (x : C) :
  linear (resolution_augmentation_section_fun x).
Proof. move=> r a b; by rewrite /resolution_augmentation_section_fun scalerDl scalerA. Qed.

HB.instance Definition _ x := GRing.isLinear.Build R [the lmodType R of R^o]
  (resolution_term_obj (C := C) R 0 x) _
  (resolution_augmentation_section_fun x) (resolution_augmentation_section_linear x).

Lemma resolution_augmentation_section (x : C) (r : R^o) :
  resolution_augmentation_fun x (resolution_augmentation_section_fun x r) = r.
Proof.
rewrite /resolution_augmentation_section_fun linearZ resolution_augmentation_basis; exact: mulr1.
Qed.

End Augmentation.
End DiazParkBarResolutionAugmentation.






