(** The literal one-point simplicial set and its actual augmented chain contraction. *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra boolp.
From DiazPark Require Import Category CategoryExtensionality BarFreeModule.
From DiazParkV16b Require Import ChainComplex SimplicialSet SimplicialSetOperators
  SimplicialChains SimplicialChainsMaps SimplicialConeContraction SimplicialReplacementConstants.
Set Universe Polymorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory DiazParkFreeModule DPChainComplex DPSimplicialSet DPSimplicialOperators
  DPSimplicialChains DPSimplicialChainMaps DPSimplicialConeContraction
  DPSimplicialReplacementConstants.
Local Open Scope ring_scope.

Module DPConstantSimplicialPointChains.
Definition point@{u v} : simplicial_set@{v u} := constant_simplicial@{u v} unit.

Definition to_point (X : simplicial_set) : simplicial_map X point.
Proof.
refine (@Build_nat_trans _ _ X point (fun _ _ => tt) _); reflexivity.
Defined.

Lemma to_point_unique (X : simplicial_set) (f : simplicial_map X point) : f = to_point X.
Proof. apply nat_trans_ext=> n; apply functional_extensionality_dep=> x; by case: (component f n x). Qed.

Definition point_cone (n : nat) (x : simplex point n) : simplex point n.+1 := x.
Arguments point_cone n x : clear implicits.

Lemma point_cone_face_zero n x : @indexed_face point n 0 (point_cone n x) = x.
Proof. reflexivity. Qed.

Lemma point_cone_face_successor n (i : 'I_n.+2) x :
  @indexed_face point n.+1 i.+1 (point_cone n.+1 x) = point_cone n (@indexed_face point n i x).
Proof. reflexivity. Qed.

Unset Universe Polymorphism.
Section Chains.
Variable R : pzRingType.

Definition point_section (r : R^o) : term R point 0%N := (r : R) *: free_basis R tt.

Lemma point_section_linear : linear point_section.
Proof. move=> a x y; by rewrite /point_section scalerDl scalerA. Qed.
HB.instance Definition _ := GRing.isLinear.Build R _ _ _ point_section point_section_linear.

Lemma point_sectionK r : augmentation R point (point_section r) = r.
Proof. rewrite /point_section linearZ augmentation_basis; exact: mulr1. Qed.

Lemma point_cone_last x : free_basis R (@indexed_face point 0 1 (point_cone 0 x)) =
  point_section (augmentation R point (free_basis R x)).
Proof. case: x; by rewrite augmentation_basis /point_section scale1r. Qed.

Theorem point_zero_exact (a : term R point 0%N) :
  augmentation R point a = 0 -> @DPChainComplex.boundary R (chains R point) 0 a.
Proof.
exact (@cone_augmentation_exact R point point_cone point_cone_face_zero
  [the lmodType R of R^o] (augmentation R point)
  (point_section : {linear _ -> _}) point_cone_last a).
Qed.

Theorem point_positive_exact n (a : chain_term (chains R point) n.+1) :
  @cycle R (chains R point) n.+1 a -> @DPChainComplex.boundary R (chains R point) n.+1 a.
Proof.
exact (@cone_positive_exact R point point_cone point_cone_face_zero point_cone_face_successor n a).
Qed.
End Chains.
End DPConstantSimplicialPointChains.
