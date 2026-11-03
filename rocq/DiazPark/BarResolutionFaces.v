From mathcomp Require Import all_boot all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality CategoryModules
  BarPaths BarFreeModule BarResolutionTerms BarResolutionHom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkBarPaths DiazParkFreeModule
  DiazParkBarResolutionTerms DiazParkBarResolutionHom.
Local Open Scope ring_scope.

Module DiazParkBarResolutionFaces.

Section Faces.
Variable R : pzRingType.
Variable C : category.

Lemma path_face_precompose n i x y (f : hom C x y) (p : path_from n.+2 y) :
  @path_inner_face C n.+1 i x (@path_precompose C n.+1 x y f p) =
    @path_precompose C n x y f (@path_inner_face C n.+1 i y p).
Proof.
case: p => z [g q]; case: i => [|i].
- case: q => w [h t]. by rewrite /= compose_assoc.
- reflexivity.
Qed.

Definition resolution_face_component (n i : nat) (x : C) :
    module_hom (fobj (@resolution_term R C n.+1) x)
      (fobj (@resolution_term R C n) x) :=
  module_hom_of_linear (free_map R (@path_inner_face C n.+1 i x)).

Definition resolution_face (n i : nat) :
    nat_trans (@resolution_term R C n.+1) (@resolution_term R C n).
Proof.
refine (@Build_nat_trans (opposite C) (module_category R)
  (@resolution_term R C n.+1) (@resolution_term R C n)
  (resolution_face_component n i) _).
move=> x y f; apply free_module_hom_ext => p.
change (free_map R (@path_inner_face C n.+1 i y)
    (free_map R (@path_precompose C n.+1 y x f) (free_basis R p)) =
  free_map R (@path_precompose C n y x f)
    (free_map R (@path_inner_face C n.+1 i x) (free_basis R p))).
rewrite !free_map_basis.
by rewrite path_face_precompose.
Defined.

Lemma resolution_face_basis n i (x : C) (p : path_from (C := C) n.+2 x) :
  module_hom_fun (component (resolution_face n i) x) (free_basis R p) =
    free_basis R (@path_inner_face C n.+1 i x p).
Proof. exact: free_map_basis. Qed.

Lemma resolution_faces n i j :
  (i <= j)%coq_nat -> (j <= n.+1)%coq_nat ->
  nat_comp (resolution_face n.+1 i) (resolution_face n j) =
    nat_comp (resolution_face n.+1 j.+1) (resolution_face n i).
Proof.
move=> hij hj; apply nat_trans_ext => x; apply free_module_hom_ext => p.
change (free_map R (@path_inner_face C n.+1 j x)
    (free_map R (@path_inner_face C n.+2 i x) (free_basis R p)) =
  free_map R (@path_inner_face C n.+1 i x)
    (free_map R (@path_inner_face C n.+2 j.+1 x) (free_basis R p))).
rewrite !free_map_basis.
by rewrite (@path_inner_faces C n.+1 i j x p hij hj).
Qed.

End Faces.
End DiazParkBarResolutionFaces.
